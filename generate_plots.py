#!/usr/bin/env python3
"""
MaxSAT Evaluation 2024 Analytics & Plotting Engine

Author: Milan Adhikari (milan.adhikari@iis.fraunhofer.de)
Year: 2026
Description: Modular visualization pipeline for generating standardized MaxSAT
             competition metrics and high-resolution cumulative cactus plots.
"""

import sys
from pathlib import Path
import matplotlib.pyplot as plt
from matplotlib.ticker import MaxNLocator
from utils.data_loader import EvaluationData


class PerformanceVisualizer:
    """modular graphics layout generator for maxsat solver benchmark evaluations."""

    def __init__(self, data_engine: EvaluationData):
        self.data = data_engine
        # academic publishing styling defaults
        plt.style.use("seaborn-v0_8-paper")
        plt.rcParams.update(
            {
                "font.size": 11,
                "axes.labelsize": 12,
                "axes.titlesize": 13,
                "xtick.labelsize": 10,
                "ytick.labelsize": 10,
                "figure.titlesize": 14,
            }
        )

    def plot_cactus(self, output_path=None):
        """builds a high-resolution cumulative cactus plot line chart."""
        cactus_data = self.data.generate_cactus_matrix()

        fig, ax = plt.subplots(figsize=(8, 5), dpi=300)

        # dynamic marker cycle to differentiate lines cleanly
        markers = ["o", "s", "^", "D", "v", "x", "*"]

        for idx, (solver, points) in enumerate(cactus_data.items()):
            if not points["x"]:
                print(f"Warning: {solver} has no solved instances to display.")
                continue

            marker = markers[idx % len(markers)]
            ax.plot(
                points["x"],
                points["y"],
                label=solver,
                marker=marker,
                # markevery=max(1, len(points["x"]) // 15),  # avoids marker crowding
                linewidth=1.8,
                markersize=5,
            )

        ax.set_title("Solver Performance Comparison (Cactus Plot)", pad=15)
        ax.set_xlabel("Number of Instances Solved")
        ax.set_ylabel("Runtime (Seconds)")
        ax.grid(True, linestyle="--", alpha=0.6)
        ax.legend(loc="upper left", frameon=True, facecolor="white", edgecolor="none")
        ax.xaxis.set_major_locator(MaxNLocator(integer=True))
        # clamp bottom axis to 0 for strict runtime tracking transparency
        ax.set_ylim(bottom=0)

        plt.tight_layout()

        if output_path:
            plt.savefig(output_path, bbox_inches="tight")
            print(f"[GRAPH SAVED] Visual target generated at: {output_path}")
        else:
            plt.show()

        plt.close()


def main():
    if len(sys.argv) < 2:
        print("Usage: python3 generate_plots.py <path_to_evaluation_results.csv>")
        sys.exit(1)

    csv_target = sys.argv[1]

    # initialize data parser class
    try:
        data_engine = EvaluationData(csv_target)
    except Exception as e:
        print(f"Error reading evaluation data file: {str(e)}")
        sys.exit(1)

    # visualization pipeline class
    visualizer = PerformanceVisualizer(data_engine)

    # clean output layout destination next to the input file
    output_png = Path(csv_target).parent / "cactus_plot.png"

    # generate graph
    visualizer.plot_cactus(output_path=output_png)


if __name__ == "__main__":
    main()
