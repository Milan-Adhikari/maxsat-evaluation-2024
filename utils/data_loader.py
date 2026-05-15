from pathlib import Path
import pandas as pd


class EvaluationData:
    """handles loading, filtering, and structuring maxsat evaluation metrics."""

    def __init__(self, csv_path):
        self.csv_path = Path(csv_path)
        self.raw_df = pd.read_csv(self.csv_path)
        self.solvers = sorted(self.raw_df["solver"].unique())

    def get_solved_runtimes(self, solver_name):
        """extracts and sorts runtimes for instances successfully solved by a specific solver."""
        solver_df = self.raw_df[self.raw_df["solver"] == solver_name]

        # filter for successful solutions (both standard complete and optimum configurations)
        solved_mask = solver_df["status"].isin(["OPTIMUM", "COMPLETE", "SATISFIABLE"])
        solved_df = solver_df[solved_mask]

        # sort runtimes ascending to calculate the cumulative cactus line data
        return sorted(solved_df["runtime_seconds"].tolist())

    def generate_cactus_matrix(self):
        """structures data specifically formatted for standard cactus plotting."""
        matrix = {}
        for solver in self.solvers:
            runtimes = self.get_solved_runtimes(solver)
            matrix[solver] = {
                "x": list(range(1, len(runtimes) + 1)),  # number of instances solved
                "y": runtimes,  # sorted execution times
            }
        return matrix
