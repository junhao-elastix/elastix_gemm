from api import *
import torch
from group_floating_point import GFPTensor, GFPDataType
from queue import Queue
from math import ceil, log2
from functools import reduce
import os

def llama_31_8b_attn():

    # GFP dtype
    gfp_data_type = GFPDataType(mantissa_bits=8, exp_bits=5, exp_bias=15, mantissa_signed=True)

    # Generating Tile Config (# Native size = 128)
    tile_config = GemmTileConfig (
        left_dtype=gfp_data_type,
        right_dtype=gfp_data_type,
        output_dtype=gfp_data_type,
        group_size=32,
        tile_groups=4,
        left_mem_depth=512,
        right_mem_depth=512,
        acc_width=58
    )

    # Instantiating external memory
    gemm_rows = 16
    gemm_cols = 16

    ext_mem = ExternalMem(
        tile_config = tile_config,
        memory_channels = gemm_rows,
        channel_bytes= 32,
        channel_depth = 16*1024*1024
    )

    # Instantiating the GEMM Array
    gemm_array = GemmArray(
        tile_config=tile_config,
        ext_mem=ext_mem,
        rows=gemm_rows,
        cols=gemm_cols
    )

    # Weights vectors
    W_q = torch.randn((4096, 4096))
    W_k = torch.randn((1024, 4096))
    W_v = torch.randn((1024, 4096))

    # Loading inputs into GEMM Array
    gfp_W_q = GFPTensor(original_shape=W_q.shape, group_axis=-1, group_size=32, dtype=gfp_data_type, original_data=W_q)
    gfp_W_k = GFPTensor(original_shape=W_k.shape, group_axis=-1, group_size=32, dtype=gfp_data_type, original_data=W_k)
    gfp_W_v = GFPTensor(original_shape=W_v.shape, group_axis=-1, group_size=32, dtype=gfp_data_type, original_data=W_v)

    ext_mem_W_q = ext_mem.write_tensor(gfp_W_q, target_address=0)
    ext_mem_W_k = ext_mem.write_tensor(gfp_W_k, target_address=ext_mem_W_q.memory_end_addr+1)
    ext_mem_W_v = ext_mem.write_tensor(gfp_W_v, target_address=ext_mem_W_k.memory_end_addr+1)
    
    # Input vector [T x 4096]
    token_vector = torch.randn((8, 4096))
    gfp_token_vector = GFPTensor(original_shape=token_vector.shape, group_axis=-1, group_size=32, dtype=gfp_data_type, original_data=token_vector)
    ext_mem_token_vector = ext_mem.write_tensor(gfp_token_vector, target_address=ext_mem_W_v.memory_end_addr+1)

    # Step 1: Compute Q
    # -------------------
    # Fetch weight matrix, right buffer, disribute across cols
    gemm_W_q = gemm_array.fetch_ext_mem_tensor(tensor_descr=ext_mem_W_q,
                                               start_ugd_idx=0,
                                               left=False,
                                               tile_mem_start_addr=0,
                                               broadcast_gemm_cols=False)
    
    # Token matrix, left buffer, broadcast to all cols
    gemm_tokens = gemm_array.fetch_ext_mem_tensor(tensor_descr=ext_mem_token_vector,
                                                   start_ugd_idx=0,
                                                   left=True,
                                                   tile_mem_start_addr=0,
                                                   broadcast_gemm_cols=True)

    # Matmul
    if not os.path.exists('Q.pt'):
        o_q = gemm_array.matmul(left=gemm_tokens, right=gemm_W_q)

        Q = gemm_array.fetch_output(o_q)

        torch.save(Q, 'Q.pt')

    else:
        Q = torch.load('Q.pt', weights_only=True)

    # Step 2 Compute K:
    # -------------------

    gemm_W_k = gemm_array.fetch_ext_mem_tensor(tensor_descr=ext_mem_W_k,
                                               start_ugd_idx=0,
                                               left=False,
                                               tile_mem_start_addr=0,
                                               broadcast_gemm_cols=False)
    
    if not os.path.exists('K.pt'):
        o_k = gemm_array.matmul(left=gemm_tokens, right=gemm_W_k)

        K = gemm_array.fetch_output(o_k)
        torch.save (K, 'K.pt')

    else:
        K = torch.load('K.pt', weights_only=True)


    # Step 3 Compute Q @ K^T             
    # ----------------------
    # Workaround - expand K 
    K_dup = torch.repeat_interleave(K, repeats=4, dim=1)
    gfp_k_dup = GFPTensor(original_shape=K_dup.shape, group_axis=-1, group_size=32, dtype=gfp_data_type, original_data=K_dup)
    k_cache_pointer = 64*1024
    k_cache_max_tokens = 8*1024
    k_cache = ext_mem.write_tensor(gfp_k_dup, target_address=k_cache_pointer)

    gfp_q = GFPTensor(original_shape=Q.shape, group_axis=-1, group_size=32, dtype=gfp_data_type, original_data=Q)
    scratch_mem_pointer = 116 * 1024
    ext_mem_Q = ext_mem.write_tensor(gfp_q, target_address=scratch_mem_pointer)

    gemm_Q = gemm_array.fetch_ext_mem_tensor(tensor_descr=ext_mem_Q,
                                             start_ugd_idx=0,
                                             broadcast_gemm_cols=True)
    

    gemm_K = gemm_array.fetch_ext_mem_tensor(tensor_descr=k_cache,
                                             start_ugd_idx=0,
                                             broadcast_gemm_cols=False)
    


    # Q & K layed out in memory. Each matrix is disributed to rows by attention head ID
    # In each row, tokens are disributed to columns. In each tile every token is represented by a single memory entry.

    # Computing attention heads (32 heads, each head 128-d) - quick and dirty for now
    
    # Potential upgrades:
    #   1. add an option to run matmul on specific ugds (when all the tensor is loaded)

    o_descr_arr = []

    attention_heads = 32
    for head_id in range (attention_heads):
        row_id = head_id % gemm_array.rows
        row_head_offset = head_id // gemm_array.rows

        entries_per_head = ceil(gemm_Q.tensor_gfp_shape[0] // gemm_array.cols)

        row_shape = torch.Size([gemm_K.tensor_gfp_shape[0], int(gemm_K.tensor_gfp_shape[1]//attention_heads), gemm_K.tensor_gfp_shape[2]])
        # ToDo: Support non even division of gfp_groups / head

        # Update gemm Q descriptor (per row)
        head_gemm_q = gemm_Q
        head_gemm_q.gemm_rows = [row_id]
        head_gemm_q.gemm_tile_start_addr = row_head_offset * entries_per_head
        head_gemm_q.tensor_gfp_shape = row_shape

        # Update gemm K descriptor (per row)
        head_gemm_k = gemm_K
        head_gemm_k.gemm_rows = [row_id]
        head_gemm_k.gemm_tile_start_addr = row_head_offset * entries_per_head
        head_gemm_k.tensor_gfp_shape = row_shape

        head_o_qk_descr = gemm_array.matmul(
            left=head_gemm_q,
            right=head_gemm_k,
            main_loop_over_left=False
        )

        o_descr_arr.append(head_o_qk_descr)

    print (len(o_descr_arr))

    #print (QK.shape)



if __name__ == "__main__":
    llama_31_8b_attn()












