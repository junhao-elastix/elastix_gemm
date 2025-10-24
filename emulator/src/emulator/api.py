from turtle import left
import torch
from group_floating_point import GFPTensor, GFPDataType
from queue import Queue
from math import ceil, log2
from functools import reduce

from concurrent.futures import ThreadPoolExecutor

def find_pad_size(size:int, divider:int) -> int:
    if size % divider != 0:
        return divider - (size % divider)
    else:
        return 0
        
class ExtMemTensorDescriptor:
    def __init__(self,
                 gfp_shape : tuple,                 # Source tensor shape
                 memory_channels: int | None,       # Destination memory row (None to disribute to all)
                 memory_start_addr : int,           # Tensor start address 
                 memory_end_addr : int,             # Tensor end address (inclusive)
                 block_vectors : int,               # Number of native vectors blocked together 
                 block_cnt : int,                   # Number of blocks
                 block_mantissa_offset : int,       # Offset of mantissa data in a block (in memory entries)
                 block_depth : int,                 # Depth of a block (in memory entries)
                 ugd_native_vectors : int,          # Number of native vectors per UGD vector (post row distribution)
                 inline_exp_storage : bool = False  # True to inline exponent storage, False to store separately
                 ):
        
        self.gfp_shape = gfp_shape
        self.memory_channels = memory_channels
        self.memory_start_addr = memory_start_addr
        self.memory_end_addr = memory_end_addr
        self.block_vectors = block_vectors
        self.block_cnt = block_cnt
        self.block_mantissa_offset = block_mantissa_offset
        self.block_depth = block_depth
        self.ugd_native_vectors = ugd_native_vectors
        self.inline_exp_storage = inline_exp_storage        

class ExternalMem:
    def __init__ (self,
                  tile_config: 'GemmTileConfig',    # Target tile configuration 
                  memory_channels: int,             # Number of memory/GEMM rows
                  channel_depth: int,               # Memory depth
                  channel_bytes: int = 32           # Smallest addressable unit (bytes)
                 ):
        
        """ External Memory 
        Layout assumption
            - Each GEMM row is mapped to a logical memory channel (memory_row)
        """

        self.tile_config = tile_config
        self.memory_channels = memory_channels                                           # = GEMM rows
        self.channel_depth = channel_depth                                               # Memory depth
        self.channel_bytes = channel_bytes                                               # Smallest addressable unit (bytes)

        # Instantiating memory (Unified memory for exp/man) - assuming int8 covers max mantissa/exp width 
        self.mem =  torch.zeros((self.memory_channels, self.channel_depth, self.channel_bytes), dtype=torch.int16)

    def write_tensor(self,
                     tensor: GFPTensor,                             # Source GFP tensor
                     target_address: int,                           # Target start address
                     row: int | None = None,                        # Destination rows, select None to disribute tensor across rows
                     block_vectors : int | None = None,             # Number of native vectors blocked together (None single block storage)
                     inline_exp_storage: bool = False               # True to inline exponent storage, False to store separately
                     ) -> ExtMemTensorDescriptor:
        
        """ Map a tensor into the memory """

        # 1. Distribute across memory rows / channels:
        # ===============================================
        if row is None:
            rows = [x for x in range(self.memory_channels)]
        else:
            rows = [row]

        # 1.1 Padding tensor to match the combined width of all memory rows (Composite native size)
        composite_vector_groups = len(rows) * self.tile_config.tile_groups  # Groups per composite native vector
        source_tensor_groups = tensor.mantissa_data_signed.size(1)                 # Number of groups for UGD vector

        pad_size = find_pad_size(source_tensor_groups, composite_vector_groups)

        # Pad grouped dimension (GD) to align with composite native size
        mantissa_data = torch.nn.functional.pad(tensor.mantissa_data_signed, (0,0, 0,pad_size))
        exp_data = torch.nn.functional.pad(tensor.exp_data, (0,0, 0,pad_size))

        # 1.2 Split tensor across memory rows [UGD, number_of_groups, groups_size] => [UGD, ugd_native_vectors, rows, native_size]
        ugd_cnt = mantissa_data.size(0)
        #source_tensor_groups = mantissa_data.size(-2) 
        #ugd_native_vectors = source_tensor_groups // composite_vector_groups # Number of memory entries per UGD vector

        mantissa_data = mantissa_data.reshape(ugd_cnt, -1, len(rows), self.tile_config.native_size)
        exp_data = exp_data.reshape(ugd_cnt, -1, len(rows), self.tile_config.tile_groups)
        ugd_native_vectors = mantissa_data.size(1)

        # Write data to row memory
        for row_idx, row in enumerate(rows):
            # Row/Channel mantissa data [UGD, ugd_native_vectors, native_size]
            row_mantissa_data = mantissa_data[:, :, row_idx, :] 

            # Row/Channel exponent data [UGD, ugd_native_vectors, tile_groups]
            row_exp_data = exp_data[:, :, row_idx, :]

            # Inline exponent storage (todo: review with block size)
            if inline_exp_storage:
                mem_data = torch.cat([row_exp_data, row_mantissa_data], dim=-1)
                mem_data = mem_data.flatten(1)
                pad_size=find_pad_size(mem_data[-1], self.tile_config.native_size)
                mem_data = torch.nn.functional.pad(mem_data, (0, pad_size)).reshape(-1, self.tile_config.native_size)

            else:
                # Split mantissa/exp data into blocks 
                # ---------------------------------
                row_native_vectors = row_mantissa_data.reshape(-1, self.tile_config.native_size)
                row_exp_data = row_exp_data.reshape(-1, self.tile_config.tile_groups)
                
                # Pad to align with block size
                block_vectors = block_vectors if block_vectors is not None else row_native_vectors.size(0) # Number of native vectors in a block
                pad_size = find_pad_size(row_native_vectors.size(0), block_vectors)
                
                # Blocked mantissa data [num_blocks, block_vectors, native_vector_size]
                blocked_mantissa_data = torch.nn.functional.pad(row_native_vectors, (0,0,0,pad_size)).reshape(-1, block_vectors, self.tile_config.native_size)

                # Blocked exponent data [num_blocks, block_vectors, tile_groups]
                blocked_exp_data = torch.nn.functional.pad(row_exp_data, (0,0,0,pad_size)).reshape(-1, block_vectors, self.tile_config.tile_groups)

                # For each block    
                current_addr = target_address

                block_cnt = blocked_mantissa_data.size(0)   

                for b in range(blocked_mantissa_data.size(0)):
                    # Store block exponents seperately (Current support for 8 bit exponent only)
                    block_exp_data = blocked_exp_data[b].reshape(-1)
                    pad_size = find_pad_size(block_exp_data.size(0), self.channel_bytes)
                    block_exp_data = torch.nn.functional.pad(block_exp_data, (0, pad_size)).reshape(-1, self.channel_bytes)

                    block_mantissa_offset = block_exp_data.size(0)

                    # Current support for 4/8 mantissa bits only
                    if tensor.dtype.mantissa_bits == 8:
                        block_mantissa_data = blocked_mantissa_data[b].reshape(-1)
                        pad_size = find_pad_size(block_mantissa_data.size(0), self.channel_bytes)
                        block_mantissa_data = torch.nn.functional.pad(block_mantissa_data, (0, pad_size)).reshape(-1, self.channel_bytes)

                        block_depth = block_exp_data.size(0) + block_mantissa_data.size(0)

                    elif tensor.dtype.mantissa_bits == 4:    
                        # ToDo: Add support
                        raise ValueError("4 bit mantissa storage is not yet supported")

                    else:
                        raise ValueError("Currently only 4/8 bit mantissa supported for blocked storage")
                        
                    mem_data = torch.cat([block_exp_data, block_mantissa_data], dim=0)

                    self.mem[row][current_addr: current_addr + mem_data.size(0)] = mem_data
                    current_addr += mem_data.size(0)

        
        # Return tensor descriptor:
        # --------------------------
        tensor_dscr = ExtMemTensorDescriptor (
            gfp_shape = tensor.mantissa_data_signed.shape,
            memory_channels = rows,
            memory_start_addr= target_address,
            memory_end_addr = current_addr - 1,
            block_vectors = block_vectors,
            block_cnt = block_cnt,
            block_mantissa_offset = block_mantissa_offset,
            block_depth = block_depth,
            ugd_native_vectors = ugd_native_vectors,
            inline_exp_storage = inline_exp_storage
        )

        return tensor_dscr
    
    def append_tensor(self,
                      mem_tensor: ExtMemTensorDescriptor,
                      tensor: GFPTensor, # Source GFP tensor
                      ) -> ExtMemTensorDescriptor:
        
        # ToDo: Check compatibilty
        # ToDo: Check space availability 

        #for row_idx, row in enumerate(mem_tensor.memory_row):
        pass


class GemmTileConfig:
    def __init__(self,
                 left_dtype: GFPDataType,
                 right_dtype: GFPDataType,
                 output_dtype: GFPDataType,
                 group_size: int = 32,              # Number of elements in a group
                 tile_groups: int = 4,              # Number of groups in a tile    
                 left_mem_depth: int = 128,         # Depth of left memory  
                 right_mem_depth: int = 128,        # Depth of right memory
                 acc_width: int = 58,               # Width of the accumulator
                 ) -> None: 
        
        self.left_dtype = left_dtype
        self.right_dtype = right_dtype
        self.output_dtype = output_dtype
        self.group_size = group_size
        self.tile_groups = tile_groups
        self.tile_size = group_size * tile_groups
        self.left_mem_depth = left_mem_depth
        self.right_mem_depth = right_mem_depth
        self.acc_width = acc_width  
        self.native_size = group_size * tile_groups

class GemmTile:

    def __init__ (self,
                  config: GemmTileConfig,
                  o_queue: Queue = None
                  ):
    
        self.config = config  # Compile time configuration

        # Instantiating memory - assuming int16 covers max mantissa/exp width
        self.left_mem = torch.zeros((self.config.left_mem_depth, self.config.native_size), dtype=torch.int16)
        self.right_mem = torch.zeros((self.config.right_mem_depth, self.config.native_size), dtype=torch.int16)

        self.left_exp = torch.zeros((self.config.left_mem_depth, self.config.tile_groups), dtype=torch.uint8)
        self.right_exp = torch.zeros((self.config.right_mem_depth, self.config.tile_groups), dtype=torch.uint8)

        self.acc = 0

        if o_queue is None:
            self.o_queue = Queue()

    def write_tensor(self,
                     data: GFPTensor = None,
                     left : bool = True,
                     start_idx: int = 0
                     ) -> None:
        
        """ Write GFPTensor data to tile memory """

        # Check data type:
        if not isinstance(data, GFPTensor):
            raise TypeError("Data must be a GFPTensor")
        
        # Check config:
        if left and data.dtype != self.config.left_dtype:
            raise ValueError("Left data type mismatch")
        if not left and data.dtype != self.config.right_dtype:
            raise ValueError("Right data type mismatch")
        
        if self.config.group_size != data.group_size:
            raise ValueError("Group size mismatch")
        
        self.write_memory(
            left=left,
            mantissa_data=data.mantissa_data_signed,
            exp_data=data.exp_data,
            start_idx=start_idx
            )

    def write_memory(self,
                     left : bool,
                     mantissa_data: torch.Tensor|None,
                     exp_data: torch.Tensor|None,
                     start_idx: int = 0
                     ) -> None:
        
        """ Populate tile memory with explicit mantissa and exponent data """
        
        if mantissa_data is not None:
            # Pad and reshape to align with Native tile size
            data = mantissa_data.reshape(-1)
            #pad_size = self.config.native_size - (data.size(0) % (self.config.native_size))
            pad_size = find_pad_size(data.size(0), self.config.native_size)
            data = torch.nn.functional.pad(data, (0, pad_size))
            data = data.view(-1, self.config.native_size)

        if exp_data is not None:
            # Pad and reshape to align with Native tile size
            exp = exp_data.reshape(-1)
            #pad_exp_size = self.config.tile_groups - (exp.size(0) % self.config.tile_groups)
            pad_exp_size = find_pad_size(exp.size(0), self.config.tile_groups)
            exp = torch.nn.functional.pad(exp, (0, pad_exp_size))
            exp = exp.view(-1, self.config.tile_groups)

        if left:
            if mantissa_data is not None:
                self.left_mem[start_idx:start_idx + data.size(0)] = data
            if exp_data is not None:
                self.left_exp[start_idx:start_idx + exp.size(0)] = exp

        else:
            if mantissa_data is not None:
                self.right_mem[start_idx:start_idx + data.size(0)] = data
            if exp_data is not None:
                self.right_exp[start_idx:start_idx + exp.size(0)] = exp

    def _atomic_multiply(self, 
                         left_idx: int,                     # Left memory index
                         right_idx: int,                    # Right memory index
                         vector_width: int | None = None    # Number of elements to include in the multiplication
                         ) -> int:
        
        """ Single cycle (pipelined) tile level multiplication """
 
        if vector_width is None:
            vector_width = self.config.native_size

        if vector_width > self.config.native_size:
            raise ValueError("Vector width exceeds native size")
        
        left_data = self.left_mem[left_idx].view(self.config.tile_groups, self.config.group_size)
        right_data = self.right_mem[right_idx].view(self.config.tile_groups, self.config.group_size)
        
        sum = 0

        active_groups = ceil(vector_width / self.config.group_size)
        active_elements = vector_width
        
        # Iterate over tile groups
        for grp in range(active_groups):
            left_mantissa = left_data[grp]
            right_mantissa = right_data[grp]    
            
            # Perform the multiplication
            product = left_mantissa.to(torch.int64) * right_mantissa.to(torch.int64)
            
            # Mask out inactive elements
            if active_elements < self.config.group_size:
                product[vector_width:] = 0 
            
            # Add all results
            dotp = int(reduce(lambda x, y: x + y, product))
            
            # compute exponent 
            product_exp = self.left_exp[left_idx][grp] + self.right_exp[right_idx][grp]

            # Accumulate the result
            sum += dotp * pow(2, product_exp.item())  
            active_elements -= self.config.group_size

        return sum

    def _normalize_acc(self) -> tuple[int, int]:
        # Normalize the accumulated result
        if self.acc != 0:
            bits = ceil(log2(abs(self.acc)+1))

        else:
            bits = 0
        
        
        exp = (bits 
               + self.config.output_dtype.exp_bias 
               - self.config.output_dtype.mantissa_bits 
               - self.config.left_dtype.exp_bias 
               - self.config.right_dtype.exp_bias)
        
        #shift = b1 - e1 - 2*b0 # = mbits - ceil(log2(abs(acc)))
        shift =  self.config.output_dtype.mantissa_bits - bits
        
        if shift < 0:
            man = self.acc >> -shift
        else:
            man = self.acc << shift

        return (exp, man)
    
    def matmul(self,
               left_start_addr: int = 0,                    # Start memory address in left tile memory
               right_start_addr: int = 0,                   # Start memory address in right tile memory
               left_vectors: int = 16,                      # Number of left UGD vectors to process
               right_vectors: int = 8,                      # Number of right UGD vectors to process
               main_loop_over_left: bool = True,            # Loop ordering 
               ugd_vector_size: int | None = None,          # Number of elements in a vector (# None for native size)
                                                            # (Elements in grouped dimenstion before grouping)
                                                            # Data always padded to native size
               dynamic_ugd_size_init: int | None = None,
               dynamic_ugd_size_step: int | None = None,

               ) -> None:
        
        if ugd_vector_size is None:
            ugd_vector_size = self.config.native_size

        # Compute number of Native Vectors required to represent an ungrouped vector
        vector_addr_step  = ceil(ugd_vector_size / self.config.native_size)

        # main loop over left
        if main_loop_over_left:
            for l in range(left_start_addr, left_start_addr + left_vectors):
                for r in range(right_start_addr, right_start_addr + right_vectors):
                    
                    # Fixed tensor length
                    if dynamic_ugd_size_init is None:
                        tensor_length = ugd_vector_size

                    # Dynamic tensor length
                    else:
                        tensor_length = dynamic_ugd_size_init + (l * dynamic_ugd_size_step)

                    self.acc = 0
                    vector_offset = 0   
                    
                    while tensor_length > 0:
                        self.acc += self._atomic_multiply(
                            left_idx = vector_addr_step * l + vector_offset,
                            right_idx = vector_addr_step * r + vector_offset,
                            vector_width= min(tensor_length, self.config.native_size)
                            )
                        tensor_length -= self.config.native_size
                        vector_offset += 1
                    
                    self.o_queue.put(self._normalize_acc())
        
        # main loop over right
        else: 
            for r in range(right_start_addr, right_start_addr + right_vectors):
                for l in range(left_start_addr, left_start_addr + left_vectors):
                    
                    # Fixed tensor length
                    if dynamic_ugd_size_init is None:
                        tensor_length = ugd_vector_size

                    # Dynamic tensor length
                    else:
                        tensor_length = dynamic_ugd_size_init + (l * dynamic_ugd_size_step)

                    self.acc = 0
                    vector_offset = 0
                    
                    while tensor_length > 0:
                        self.acc += self._atomic_multiply(
                            left_idx = vector_addr_step * l + vector_offset,
                            right_idx = vector_addr_step * r + vector_offset,
                            vector_width= min(tensor_length, self.config.native_size)
                            )
                        tensor_length -= self.config.native_size
                        vector_offset += 1
                    
                    self.o_queue.put(self._normalize_acc())

class GemmTensorDescriptor:
    def __init__(self,
                 # Original tensor 
                 tensor_gfp_shape : tuple,      # Original GFP mantissa shape
                 
                 # Tensor slice information 
                 tensor_ugd_start_idx: int,     # Start index on the leftmost dimension (ungrouped)
                 tensor_ugd_cnt: int,           # Number of tensors on the ungrouped dimension (UGD)
                 
                 # GEMM location information 
                 left: bool,                    # Left or right tile memory
                 gemm_rows: list,               # Gemm ROWs that hold the tensor 
                 gemm_tile_start_addr: int,     # Gemm Memory start address
                 broadcast_gemm_cols: bool,     # Tensor broadcasted across columns (otherwise distributed)
                 ) -> None:

        self.tensor_gfp_shape = tensor_gfp_shape
        self.tensor_ugd_start_idx = tensor_ugd_start_idx
        self.tensor_ugd_cnt = tensor_ugd_cnt
        self.left = left
        self.gemm_rows = gemm_rows
        self.gemm_tile_start_addr = gemm_tile_start_addr
        self.broadcast_gemm_cols = broadcast_gemm_cols
        self.ugd_vector_size = tensor_gfp_shape[-1] * tensor_gfp_shape[-2] # Number of elements in ungrouped dimension (vector size)      

class GemmOutputDescriptor:
    def __init__(self,
                 rows: int | None,    # Participating rows (None for all)
                 dim0: int,           # How many column fetches to get 1st dim
                 dim1: int,
                ):
        
        self.rows = rows
        self.dim0 = dim0
        self.dim1 = dim1
        
class GemmArray:
# To Do: Generalize design (one memory space - left/right different memory sections ?)

    def __init__(self,
                 tile_config: GemmTileConfig,
                 rows: int = 16,
                 cols: int = 16,
                 ext_mem: ExternalMem|None = None
                 ) -> None:
        self.tile_config = tile_config
        self.rows = rows
        self.cols = cols
        self.ext_mem = ext_mem

        # Tile instantiation
        self.tiles = [[GemmTile(tile_config) for _ in range(cols)] for _ in range(rows)]

    def fetch_ext_mem_tensor (self,
                      # Source parameters
                      tensor_descr: ExtMemTensorDescriptor,
                      start_ugd_idx : int,           # Start UGD index
                      ugd_cnt : int | None = None,   # Number of UGD elements to fetch, None for all

                      # Destination parameters
                      left: bool = True, 
                      tile_mem_start_addr: int = 0,
                      broadcast_gemm_cols : bool = False,  # Broadcast tensor to all columns, otherwise distribute
                    ) -> GemmTensorDescriptor:
                    
        """ Fetch tensor data from the GEMM array """
        
        if ugd_cnt is None:
            ugd_cnt = tensor_descr.gfp_shape[0] - start_ugd_idx
        
        
        # Find native vector indexes to read
        first_nvector_idx = start_ugd_idx * tensor_descr.ugd_native_vectors
        last_nvector_idx = (start_ugd_idx + ugd_cnt) * tensor_descr.ugd_native_vectors - 1

        # Find relative block indexes
        first_block_idx = first_nvector_idx // tensor_descr.block_vectors
        first_block_offset = first_nvector_idx % tensor_descr.block_vectors

        last_block_idx = last_nvector_idx // tensor_descr.block_vectors
        last_block_offset = last_nvector_idx % tensor_descr.block_vectors


        row_mantissa_data = [None for _ in range(self.rows)]
        row_exp_data = [None for _ in range(self.rows)] 

        # Looping over blocks to extract data 
        for block in range(first_block_idx, last_block_idx + 1):
            # Compute block read boundaries
            if block == first_block_idx:
                block_start_offset = first_block_offset
            else:
                block_start_offset = 0
            
            if block == last_block_idx:
                block_end_offset = last_block_offset
            else:
                block_end_offset = tensor_descr.block_vectors - 1
            

            for row in tensor_descr.memory_channels:
                block_start_address = tensor_descr.memory_start_addr + block * tensor_descr.block_depth
                block_end_address = block_start_address + tensor_descr.block_depth - 1
                block_data = self.ext_mem.mem[row][block_start_address:block_end_address + 1]

                block_mantissa = block_data[tensor_descr.block_mantissa_offset: tensor_descr.block_depth]
                block_exp = block_data[0:tensor_descr.block_mantissa_offset]

                # Reshape to fit native vector size:
                block_mantissa = block_mantissa.reshape(-1, self.tile_config.native_size) [block_start_offset:block_end_offset + 1]
                block_exp = block_exp.reshape(-1, self.tile_config.tile_groups) [block_start_offset:block_end_offset + 1]


                # Append to row data
                if row_mantissa_data[row] is None:
                    row_mantissa_data[row] = block_mantissa
                    row_exp_data[row] = block_exp
                else:
                    row_mantissa_data[row] = torch.cat([row_mantissa_data[row], block_mantissa], dim=0)
                    row_exp_data[row] = torch.cat([row_exp_data[row], block_exp], dim=0)


        # Writing into tile memory
        for row in tensor_descr.memory_channels:
            
            # Broadcast to all columns
            if broadcast_gemm_cols:
                for col in range(self.cols):
                    self.tiles[row][col].write_memory(
                        left=left,
                        start_idx=tile_mem_start_addr,
                        mantissa_data=row_mantissa_data[row],
                        exp_data=row_exp_data[row]                        
                    )

            # Distribute UGDs across columns 
            else: 
                mantissa_data = row_mantissa_data[row].reshape(ugd_cnt, -1, self.tile_config.native_size)
                exp_data = row_exp_data[row].reshape(ugd_cnt, -1, self.tile_config.tile_groups)
                for col in range(self.cols):
                    self.tiles[row][col].write_memory(
                        left=left,
                        start_idx = tile_mem_start_addr,
                        mantissa_data=mantissa_data[col::self.cols],
                        exp_data=exp_data[col::self.cols]
                    )

        # Return a tensor descriptor
        gemm_tensor_descr = GemmTensorDescriptor(
            tensor_gfp_shape = tensor_descr.gfp_shape,

            # Tensor slice information
            tensor_ugd_start_idx = start_ugd_idx,
            tensor_ugd_cnt = ugd_cnt,
                 
            # GEMM location information 
            left = left,
            gemm_rows = tensor_descr.memory_channels,
            gemm_tile_start_addr = tile_mem_start_addr,
            broadcast_gemm_cols = broadcast_gemm_cols
        )

        return gemm_tensor_descr

    def distribute_tensor(self,
                          left : bool,                        # True for left tensor, False for right tensor
                          tensor: GFPTensor,                  # Data to distribute
                          target_gemm_row: int | None = None, # Target row in the GEMM array - use None to distribute to all
                          broadcast_gemm_cols : bool = False, # Broadcast to all GEMM columns, otherwise distributed across columns 
                          tile_mem_start_addr: int = 0,       # Start address in tile memory (destination)
                          tensor_ugd_start_idx: int = 0,      # First column/rows (Ungrouped Dimension - UGD) to read (must be a multiple of the gemm array column)
                          tensor_ugd_cnt: int | None = None,  # Number of columns/rows (UGD) to read (None for all columns)
                          ) -> GemmTensorDescriptor:
        """ 
        Reference / Debug function 

        Populate GEMM array with tensor data. 
        
        Assuming a 2d [ungrouped_dim, grouped_dim] ([rows, cols]  or [cols, rows]) tensor that has the last dimenstion broken into groups.
 
        """  

        # Mantissa data: [ugd, gd_group, group_size]
        if target_gemm_row is None:
            target_gemm_rows = [i for i in range(self.rows)]
        else:
            target_gemm_rows = [target_gemm_row]

        # Step 1: pad to match Array vector size (= Tile_Native_Size * GEMM_Rows)
        # --------------------------------------------------------------------
        groups = tensor.mantissa_data_signed.size(1)                          # Number of groups for UGD tensor

        array_vector_groups = self.tile_config.tile_groups * len(target_gemm_rows)         # Number of groups in GEMM array column 

        if groups % array_vector_groups != 0:
            pad_size = array_vector_groups - (groups % array_vector_groups)
        else:
            pad_size = 0
        
        # Pad group dimension (2nd dimension)
        # -------------------------------------
        mantissa_data = torch.nn.functional.pad(tensor.mantissa_data_signed, (0,0, 0,pad_size))
        exp_data = torch.nn.functional.pad(tensor.exp_data, (0,0, 0,pad_size))

        # Step 2: Split groups to align with tile size 
        # -----------------------------------------------
        groups_cnt = mantissa_data.size(-2) 
        tile_native_size_groups = groups_cnt // self.tile_config.tile_groups  # Number of groups in a tile's native size

        # Add a dimension to represent tile native size
        mantissa_data = mantissa_data.unflatten(-2, sizes = (tile_native_size_groups, self.tile_config.tile_groups))
        exp_data = exp_data.unflatten(-2, sizes = (tile_native_size_groups, self.tile_config.tile_groups))


        # Step 3: Distribute among tiles  
        # --------------------------------
        if not broadcast_gemm_cols and tensor_ugd_start_idx % self.cols != 0:
            raise ValueError("First column must be a multiple of the number of columns in the GEMM array unless broadcasting is enabled")

        # Determine UGD count (None for all)
        if tensor_ugd_cnt is None:
            tensor_ugd_cnt = mantissa_data.size(0)

        for tile_col_id in range(self.cols):
            for row_idx, tile_row_id in enumerate(target_gemm_rows):
                # Distribute across columns
                if not broadcast_gemm_cols:
                    # Silce tile specific data
                    tile_mantissa_data = mantissa_data[tile_col_id::self.cols, row_idx::len(target_gemm_rows)]
                    tile_exp_data = exp_data[tile_col_id::self.cols, row_idx::len(target_gemm_rows)]

                    # Compute start and end column on tile data
                    first_col = tensor_ugd_start_idx // self.cols                  # First col out of every tile tensor
                    col_cnt = ceil((tensor_ugd_cnt - tile_col_id) / self.cols)
                    last_col = first_col + col_cnt 

                # Broadcast to all columns
                else:
                    # Silce tile specific data
                    tile_mantissa_data = mantissa_data[: , row_idx::len(target_gemm_rows)]
                    tile_exp_data = exp_data[: , row_idx::len(target_gemm_rows)]

                    # Compute start and end column on tile data
                    first_col = tensor_ugd_start_idx   # First col out of every tile tensor
                    col_cnt = tensor_ugd_cnt
                    last_col = first_col + col_cnt 
               
                if col_cnt > 0:
                    # Write to tile memory
                    self.tiles[tile_row_id][tile_col_id].write_memory(
                        left = left,
                        start_idx = tile_mem_start_addr,
                        mantissa_data = tile_mantissa_data[first_col: last_col],
                        exp_data = tile_exp_data[first_col: last_col]
                    )
        
        # Return a tensor descriptor
        # ---------------------
        tensor_descriptor = GemmTensorDescriptor(
            # Tensor information
            tensor_gfp_shape=tensor.mantissa_data_signed.shape,
            tensor_ugd_start_idx=tensor_ugd_start_idx,
            tensor_ugd_cnt=tensor_ugd_cnt,
            
            # Gemm Mapping information 
            left=left,
            gemm_rows=target_gemm_rows,
            gemm_tile_start_addr=tile_mem_start_addr,
            broadcast_gemm_cols=broadcast_gemm_cols
        )

        return tensor_descriptor

    def _raw_matmul(
            self,
            active_gemm_rows: list[int]|None,           # List of active GEMM rows, use None for all 
               
            left_start_addr: int = 0,                   # Start index for left tensor (same for all tiles)
            right_start_addr: int = 0,                  # Start index for right tensor (same for all tiles)
                    
            total_left_gemm_col_vectors: int = 16,      # Number of total lhs gemm column vector to process (broadcasted/distributed across gemm cols)
            total_right_gemm_col_vectors: int = 16,     # Number of total rhs gemm columns vector to process (broadcasted/distributed gemm cols)
                    
            main_loop_over_left: bool = True,           # Loop ordering (for each tile)

            gemm_ugd_vector_size : int = 1,             # Number of elements per UGD in an entire gemm_col (across all rows)

            dynamic_ugd_size_init: int | None = None,
            dynamic_ugd_size_step: int | None = None,

            ) -> None:
        
        """ Perform matmul operation across active tiles """
        
        if active_gemm_rows is None:
            active_gemm_rows = [i for i in range(self.rows)]

        row_cnt = len(active_gemm_rows)

        # Compute number of UGD vectors processed in each gemm column:
        col_left_vectors =  [ceil((total_left_gemm_col_vectors - col_id)/ self.cols) for col_id in range(self.cols)]
        col_right_vectors = [ceil((total_right_gemm_col_vectors - col_id)/ self.cols) for col_id in range(self.cols)]
        
        # Computing native vector per UGD vector
        native_vecs_per_ugd_vector = ceil(gemm_ugd_vector_size / self.tile_config.native_size)
        last_native_vec_pad = native_vecs_per_ugd_vector * self.tile_config.native_size - gemm_ugd_vector_size

        thread_pool = ThreadPoolExecutor(max_workers=30)
                                         
        # Sending gemm tile commands: 
        for gemm_row_idx, tile_row_id in enumerate(active_gemm_rows):

            # Number of native vectors in each row
            row_native_vectors = ceil((native_vecs_per_ugd_vector-gemm_row_idx) / row_cnt)

            row_vector_size = row_native_vectors * self.tile_config.native_size

            # Detect last row (partial vector)
            if (native_vecs_per_ugd_vector - 1) %  row_cnt == gemm_row_idx:
                row_vector_size = row_vector_size - last_native_vec_pad

            #row_vector_size = ceil((gemm_ugd_vector_size - gemm_row_idx) / self.rows)
            row_vector_size 



            for tile_col_id in range(self.cols):

                futures = [thread_pool.submit(self.tiles[tile_row_id][tile_col_id].matmul(
                    left_start_addr = left_start_addr,
                    right_start_addr = right_start_addr,
                    left_vectors = col_left_vectors[tile_col_id],
                    right_vectors = col_right_vectors[tile_col_id],
                    main_loop_over_left = main_loop_over_left,
                    ugd_vector_size = row_vector_size,
                    dynamic_ugd_size_init = dynamic_ugd_size_init,
                    dynamic_ugd_size_step = dynamic_ugd_size_step
                    )
                )]
                
    def matmul(
            self,
            left: GemmTensorDescriptor,
            right: GemmTensorDescriptor,
            main_loop_over_left: bool = True,

            dynamic_ugd_size_init: int | None = None,
            dynamic_ugd_size_step: int | None = None
            
            ) -> GemmOutputDescriptor:  
        
        ''' Multiply two tensors'''

        # Step 1 : check tensor compatibility 
        if left.gemm_rows != right.gemm_rows:
            raise ValueError("Incompatible tensor shapes (GEMM rows)")
        
        if left.ugd_vector_size != right.ugd_vector_size:
            raise ValueError("Incompatible tensor shapes (UGD vector size)")

        if left.broadcast_gemm_cols:
            left_col_cnt = left.tensor_ugd_cnt * self.cols
        else:
            left_col_cnt = left.tensor_ugd_cnt

        if right.broadcast_gemm_cols:
            right_col_cnt = right.tensor_ugd_cnt * self.cols
        else:
            right_col_cnt = right.tensor_ugd_cnt

        
        self._raw_matmul(
            active_gemm_rows = left.gemm_rows,
               
            left_start_addr = left.gemm_tile_start_addr,
            right_start_addr = right.gemm_tile_start_addr,
            total_left_gemm_col_vectors = left_col_cnt,
            total_right_gemm_col_vectors = right_col_cnt,
            main_loop_over_left = main_loop_over_left,
            gemm_ugd_vector_size = left.ugd_vector_size,
            dynamic_ugd_size_init = dynamic_ugd_size_init,
            dynamic_ugd_size_step = dynamic_ugd_size_step
        )

        # Normal matmul - left is broadcasted, right is distributed
        if left.broadcast_gemm_cols and right.broadcast_gemm_cols == False:
            left_ugd = left.tensor_ugd_cnt
            right_ugd = right.tensor_ugd_cnt

            total_results = left_ugd * right_ugd

            if main_loop_over_left:
                dim0 = right_ugd
                dim1 = left_ugd
            
            else:
                dim0 = right_ugd
                dim1 = left_ugd

        # Non-broadcast - not supported
        else:
            raise ValueError("Not yet supported")
    
        output_descr = GemmOutputDescriptor(
            rows = left.gemm_rows,
            dim0 = dim0,    
            dim1 = dim1
        )

        return output_descr
    
    def fetch_output(self,
                     tesnor_descr : GemmOutputDescriptor) -> torch.Tensor:
        
        gemm_res = torch.zeros((tesnor_descr.dim1, tesnor_descr.dim0), dtype=torch.float32)
    
        for r in range(tesnor_descr.dim1):
            for c in range(tesnor_descr.dim0):
                num = 0
                for j in tesnor_descr.rows:
                    exp, man = self.tiles[j][c%self.cols].o_queue.get()
                    num = num + pow(2, exp - self.tile_config.output_dtype.exp_bias) * man

                gemm_res[r,c] = num

        return gemm_res

class RowVectorUnit:

    def __init__(self, 
                 input_queues: list[Queue],
                 tile_config: GemmTileConfig,
                 output_dtype: GFPDataType,
                 output_mem_depth: int = 512
                 ):
        self.input_queues = input_queues
        self.tile_config = tile_config
        self.output_dtype = output_dtype

        # Instantiate output memory
        self.output_mem = torch.zeros((output_mem_depth, self.tile_config.native_size), dtype=torch.int16)
        self.output_exp_mem = torch.zeros((output_mem_depth, self.tile_config.tile_groups), dtype=torch.uint8)

def test_arr_write():
    """ Test GEMM Array write and distribution """
    gfp_data_type = GFPDataType(mantissa_bits=8, exp_bits=5, exp_bias=15, mantissa_signed=True)

    # Generating Tile Config (# Native size = 16)
    tile_config = GemmTileConfig (
        left_dtype=gfp_data_type,
        right_dtype=gfp_data_type,
        output_dtype=gfp_data_type,
        group_size=4,
        tile_groups=4,
        left_mem_depth=128,
        right_mem_depth=128,
        acc_width=58
    )

    # Generating GEMM Array (GEMM column vector size = 16 * 4 = 64))
    gemm_array = GemmArray(tile_config, rows=4, cols=5)

    # Generating 30 x 128 tensor
    o_tensor = torch.ones((30, 128), dtype=torch.float32)
    #o_tensor = torch.ones((9, 128), dtype=torch.float32)

    gpf_tensor = GFPTensor(original_shape=o_tensor.shape, group_axis=-1, group_size=4, dtype=gfp_data_type, original_data=o_tensor)

    # Updating mantissa for visualization
    for ug in range(gpf_tensor.mantissa_data_signed.size(0)):
        for g in range(gpf_tensor.mantissa_data_signed.size(1)):
            gpf_tensor.mantissa_data[ug,g][0] = ug
            gpf_tensor.mantissa_data[ug,g][1] = g

    # Distribute data to GEMM Array
    gemm_array.distribute_tensor(
        left=False,
        tensor=gpf_tensor,
        tile_mem_start_addr=0,
        tensor_ugd_start_idx=0,
        tensor_ugd_cnt=None
    )

    for row_id,r in enumerate(gemm_array.tiles):
        for col_id, c in enumerate(r):
            print(f"Tile[{row_id},{col_id}] - Right Mem: \n{c.right_mem[0:12]}")
    
def test_gemm_matmul0():
    gfp_data_type = GFPDataType(mantissa_bits=8, exp_bits=5, exp_bias=15, mantissa_signed=True)

    # Generating Tile Config (# Native size = 16)
    tile_config = GemmTileConfig (
        left_dtype=gfp_data_type,
        right_dtype=gfp_data_type,
        output_dtype=gfp_data_type,
        group_size=4,
        tile_groups=4,
        left_mem_depth=128,
        right_mem_depth=128,
        acc_width=58
    )

    # Generating GEMM Array (GEMM column (UGD) vector size = 16 * 4 = 64))
    gemm_array = GemmArray(tile_config, 
                           rows=4, 
                           cols=5)

    torch.manual_seed(0)

    # Generating left tensor (4 x 128) tensor
    left_tensor = torch.randn((4, 128), dtype=torch.float32)
    
    # Generatig right tensor (128 x 40)
    right_tensor = torch.randn((128, 40), dtype=torch.float32)
    
    # Converting to GFP
    left_gfp_tensor = GFPTensor(original_shape=left_tensor.shape, group_axis=-1, group_size=4, dtype=gfp_data_type, original_data=left_tensor)
    right_gfp_tensor = GFPTensor(original_shape=right_tensor.shape, group_axis=-2, group_size=4, dtype=gfp_data_type, original_data=right_tensor)   

    # Loading tensors into GEMM
    left_gfp = gemm_array.distribute_tensor(
        left=True,
        tensor=left_gfp_tensor,
        target_gemm_row=None,           # Target all rows
        tile_mem_start_addr=0,
        tensor_ugd_start_idx=0,
        tensor_ugd_cnt=None,
        broadcast_gemm_cols=True
    )

    right_gfp = gemm_array.distribute_tensor(
        left=False,
        tensor=right_gfp_tensor,
        target_gemm_row=None,           # Target all rows
        tile_mem_start_addr=0,
        tensor_ugd_start_idx=0,
        tensor_ugd_cnt=None,
        broadcast_gemm_cols=False
    )

    o_descr = gemm_array.matmul(left_gfp, right_gfp)

    print (o_descr)

    # Comparing to expected 
    res = left_tensor @ right_tensor

    res_rows = res.size(0)
    res_cols = res.size(1)

    gemm_res = torch.zeros((res_rows, res_cols), dtype=torch.float32)

    for r in range(res_rows):
        for c in range(res_cols):
            num = 0
            for j in range (gemm_array.rows):
                exp, man = gemm_array.tiles[j][c%gemm_array.cols].o_queue.get()
                num = num + pow(2, exp - gfp_data_type.exp_bias) * man

            gemm_res[r,c] = num
    
    print((gemm_res - res).max(), (gemm_res - res).abs().mean())
    
def test_tile():
    gfp_data_type = GFPDataType(mantissa_bits=8, exp_bits=5, exp_bias=15, mantissa_signed=True)

    # Generating tile
    tile_config = GemmTileConfig (
        left_dtype=gfp_data_type,
        right_dtype=gfp_data_type,
        output_dtype=gfp_data_type,
        group_size=10,
        tile_groups=4,
        left_mem_depth=128,
        right_mem_depth=128,
        acc_width=58
    )

    # Generating FPG tensor 
    left_tensor = torch.tensor([x/100 for x in range (80)])   # [80]
    right_tensor = torch.tensor([x/125 for x in range (8*80)]).view(8,80) # [8, 80]

    left_gfp_tensor = GFPTensor(original_shape=left_tensor.shape, group_axis=-1, group_size=10, dtype=gfp_data_type, original_data=left_tensor)
    right_gfp_tensor = GFPTensor(original_shape=right_tensor.shape, group_axis=-1, group_size=10, dtype=gfp_data_type, original_data=right_tensor)
    
    tile = GemmTile(config=tile_config)
    
    tile.write_tensor(left=True, data=left_gfp_tensor, start_idx=0)
    tile.write_tensor(left=False, data=right_gfp_tensor, start_idx=0)

    tile.matmul(left_start_addr=0, right_start_addr=0, left_vectors=1, right_vectors=8, main_loop_over_left=True, ugd_vector_size=80)

    print("Output shape:", tile.o_queue.qsize())

    res = torch.matmul(left_tensor, right_tensor.transpose(0,1))
    for i in range(tile.o_queue.qsize()):
        exp, man = tile.o_queue.get()
        print("Result from tile:", res[i], man * pow(2, exp - tile.config.output_dtype.exp_bias))

def debug_print(gemm_array):
    print(gemm_array.tiles[0][0].left_mem[0:10])
    
def exp_memory_write():
    gfp_data_type = GFPDataType(mantissa_bits=8, exp_bits=5, exp_bias=15, mantissa_signed=True)

    # Generating Tile Config (# Native size = 16)
    tile_config = GemmTileConfig (
        left_dtype=gfp_data_type,
        right_dtype=gfp_data_type,
        output_dtype=gfp_data_type,
        group_size=4,
        tile_groups=4,
        left_mem_depth=128,
        right_mem_depth=128,
        acc_width=58
    )

    gemm_rows = 4
    gemm_cols = 5

    # Generating extrnal memory
    ext_mem = ExternalMem(
        tile_config = tile_config,
        memory_channels = gemm_rows,
        channel_depth= 16*1024*1024, # 16M vectors per channel
        channel_bytes = 32,
    )

    # Generating GEMM Array (GEMM column (UGD) vector size = 16 * 4 = 64))
    gemm_array = GemmArray(tile_config, 
                           rows=gemm_rows, 
                           cols=gemm_cols,
                           ext_mem=ext_mem)

    torch.manual_seed(0)

    # Generating left tensor (4 x 128) tensor
    left_tensor = torch.randn((4, 128), dtype=torch.float32)
    
    # Generatig right tensor (128 x 40)
    right_tensor = torch.randn((128, 40), dtype=torch.float32)
    
    # Converting to GFP
    left_gfp_tensor = GFPTensor(original_shape=left_tensor.shape, group_axis=-1, group_size=4, dtype=gfp_data_type, original_data=left_tensor)
    right_gfp_tensor = GFPTensor(original_shape=right_tensor.shape, group_axis=-2, group_size=4, dtype=gfp_data_type, original_data=right_tensor)   
   
    # Writing tensors into External memory
    left_ext_mem_dscr = ext_mem.write_tensor(
        tensor = left_gfp_tensor,
        target_address=0,
        block_vectors = None,      # Initial run - 1 block
        row = None,
    )

    right_ext_mem_dscr = ext_mem.write_tensor(
        tensor = right_gfp_tensor,
        target_address = left_ext_mem_dscr.memory_end_addr + 1,
        block_vectors = None,      # Initial run - 1 block
        row = None
    )

    # Fetching data from external memory into GEMM
    left_gfp = gemm_array.fetch_ext_mem_tensor(
        tensor_descr=left_ext_mem_dscr,
        start_ugd_idx=0,
        left = True,
        tile_mem_start_addr=0,
        broadcast_gemm_cols=True
    )

    right_gfp = gemm_array.fetch_ext_mem_tensor(
        tensor_descr=right_ext_mem_dscr,
        start_ugd_idx=0,
        left=False,
        tile_mem_start_addr=0,
        broadcast_gemm_cols=False
    )

    o_descr = gemm_array.matmul(left_gfp, right_gfp)
    print(o_descr.dim0, o_descr.dim1)
    gemm_res = gemm_array.fetch_output(o_descr) 

    # Comparing to expected 
    res = left_tensor @ right_tensor

    res_rows = res.size(0)
    res_cols = res.size(1)

    print((gemm_res - res).max(), (gemm_res - res).abs().mean())

if __name__ == "__main__":
    #test_tile()
    #test_arr_write()
    #test_gemm_matmul0()
    exp_memory_write()
    pass




    

