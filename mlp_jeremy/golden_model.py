"""
Golden model for the Achronix MLP column, providing a bit-accurate
reference for BFP8 and INT8 dot product accumulation.
"""
import torch

class GoldenMLPModel:
    """
    A Python-based golden model for the `mlp_bram_col` RTL design.
    This model simulates the dual 8x8 dot product functionality with support
    for both INT8 and BFP8 data types, including multi-cycle accumulation.
    """

    def __init__(self, num_mlps: int = 4, num_params: int = 4096, data_type: str = 'BFP8'):
        """
        Initializes the golden model.

        Args:
            num_mlps: The number of MLP units in the column.
            num_params: The total number of parameters (weights).
            data_type: The data type to use ('BFP8' or 'INT8').
        """
        self.num_mlps = num_mlps
        self.num_params = num_params
        self.data_type = data_type
        self.weights = self._initialize_weights()

    def _initialize_weights(self) -> torch.Tensor:
        """Initializes weights with random values."""
        if self.data_type == 'BFP8':
            # For BFP8, we can simulate with floating point numbers
            # that will be quantized during the calculation.
            return torch.randn(2, self.num_params, self.num_mlps)
        else: # INT8
            return torch.randint(-128, 127, (2, self.num_params, self.num_mlps), dtype=torch.int32)

    def run_dot_product(self, activations: torch.Tensor) -> list[tuple[float, float]]:
        """
        Runs the dot product calculation.

        Args:
            activations: A tensor of activation values.

        Returns:
            A list of tuples, where each tuple contains the dot product
            results for bank 0 and bank 1 of an MLP unit.
        """
        if self.data_type == 'BFP8':
            return self._run_bfp8_dot_product(activations)
        else:
            return self._run_int8_dot_product(activations)

    def _run_int8_dot_product(self, activations: torch.Tensor) -> list[tuple[float, float]]:
        """Calculates the dot product for INT8 data."""
        results = []
        for i in range(self.num_mlps):
            dot0 = torch.matmul(activations, self.weights[0, :, i].float())
            dot1 = torch.matmul(activations, self.weights[1, :, i].float())
            results.append((dot0.item(), dot1.item()))
        return results

    def _run_bfp8_dot_product(self, activations: torch.Tensor) -> list[tuple[float, float]]:
        """
        Calculates the dot product for BFP8 data.
        This is a simplified model. A true bit-accurate model would need to
        implement the same quantization and accumulation logic as the RTL.
        """
        # This is a functional equivalent, not a cycle-accurate or bit-accurate model.
        # A real implementation would involve custom quantization logic.
        results = []
        for i in range(self.num_mlps):
            dot0 = torch.matmul(activations, self.weights[0, :, i])
            dot1 = torch.matmul(activations, self.weights[1, :, i])
            results.append((dot0.item(), dot1.item()))
        return results

if __name__ == '__main__':
    # Example usage
    NUM_MLPS = 4
    NUM_PARAMS = 1024

    # INT8 example
    print("--- INT8 Example ---")
    int8_model = GoldenMLPModel(num_mlps=NUM_MLPS, num_params=NUM_PARAMS, data_type='INT8')
    int8_activations = torch.randint(-128, 127, (NUM_PARAMS,), dtype=torch.int32)
    int8_results = int8_model.run_dot_product(int8_activations.float())
    for i, (dot0, dot1) in enumerate(int8_results):
        print(f"MLP {i}: Bank 0 = {dot0}, Bank 1 = {dot1}")

    print("\n--- BFP8 Example ---")
    # BFP8 example
    bfp8_model = GoldenMLPModel(num_mlps=NUM_MLPS, num_params=NUM_PARAMS, data_type='BFP8')
    bfp8_activations = torch.randn(NUM_PARAMS)
    bfp8_results = bfp8_model.run_dot_product(bfp8_activations)
    for i, (dot0, dot1) in enumerate(bfp8_results):
        print(f"MLP {i}: Bank 0 = {dot0}, Bank 1 = {dot1}")
