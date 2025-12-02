"""
Test script for the golden model.
"""
import torch
from golden_model import GoldenMLPModel

def test_golden_model():
    """
    Tests the GoldenMLPModel to ensure it runs without errors and
    produces results of the correct shape.
    """
    num_mlps = 4
    num_params = 256

    # Test INT8
    int8_model = GoldenMLPModel(num_mlps=num_mlps, num_params=num_params, data_type='INT8')
    int8_activations = torch.randint(-128, 127, (num_params,), dtype=torch.int32)
    int8_results = int8_model.run_dot_product(int8_activations.float())
    assert len(int8_results) == num_mlps
    for res in int8_results:
        assert isinstance(res, tuple)
        assert len(res) == 2

    # Test BFP8
    bfp8_model = GoldenMLPModel(num_mlps=num_mlps, num_params=num_params, data_type='BFP8')
    bfp8_activations = torch.randn(num_params)
    bfp8_results = bfp8_model.run_dot_product(bfp8_activations)
    assert len(bfp8_results) == num_mlps
    for res in bfp8_results:
        assert isinstance(res, tuple)
        assert len(res) == 2

    print("Golden model test passed!")

if __name__ == '__main__':
    test_golden_model()
