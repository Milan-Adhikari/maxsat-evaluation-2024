#!/usr/bin/env python3
"""
MaxSAT Evaluation 2024 Execution & Benchmarking Framework

Author: Milan Adhikari (milan.adhikari@iis.fraunhofer.de)
Year: 2026
Description: Automated multi-threaded execution matrix runner and sandbox
             orchestrator for local and Slurm HPC cluster environments.
"""

import os
import sys
import subprocess
import yaml
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import tempfile
import time
from datetime import datetime
import pandas as pd
import lzma
import re

# conditionally import fcntl for linux/hpc systems to manage file locks
try:
    import fcntl
except ImportError:
    fcntl = None  # fallback handling if run on a non-posix development environment


def load_config(config_path="config.yaml"):
    with open(config_path, "r") as f:
        return yaml.safe_load(f)


def parse_optimum_value(full_output):
    """
    Parses the output text to extract the final optimum value.
    Looks for standard MaxSAT 'o ' lines, handling optional solver prefixes (like '0.00/0.00 o 177').
    Returns the integer value of the last occurrence if found, otherwise None.
    """
    # matches 'o' followed by an optional space and digits at the end of a line or after spaces.
    pattern = re.compile(r"(?:^|\s)o\s*(\d+)\s*$", re.MULTILINE)
    matches = pattern.findall(full_output)

    if matches:
        # last 'o' line in the output represents the final optimized value
        return int(matches[-1])
    return None


def append_row_atomic(row_data, file_path):
    new_df = pd.DataFrame([row_data])
    file_exists = os.path.isfile(file_path)

    with open(file_path, "a" if file_exists else "w", newline="") as f:
        if fcntl:
            fcntl.flock(f.fileno(), fcntl.LOCK_EX)

        try:
            if not file_exists:
                new_df.to_csv(f, index=False)
            else:
                existing_df = pd.read_csv(file_path, nrows=0)
                all_columns = list(
                    dict.fromkeys(list(existing_df.columns) + list(new_df.columns))
                )

                if len(all_columns) > len(existing_df.columns):
                    if fcntl:
                        fcntl.flock(f.fileno(), fcntl.LOCK_UN)

                    with open(file_path, "r+") as f_rewrite:
                        if fcntl:
                            fcntl.flock(f_rewrite.fileno(), fcntl.LOCK_EX)
                        full_df = pd.read_csv(f_rewrite)
                        full_df = pd.concat([full_df, new_df], ignore_index=True)
                        f_rewrite.seek(0)
                        f_rewrite.truncate()
                        full_df.to_csv(f_rewrite, index=False)
                    return

                new_df.reindex(columns=all_columns).to_csv(f, header=False, index=False)
        finally:
            if fcntl:
                fcntl.flock(f.fileno(), fcntl.LOCK_UN)


def append_text_log_atomic(
    solver_name, benchmark_name, status, runtime, exit_code, raw_output, logs_dir
):
    # build a distinct file for each solver
    log_file_path = Path(logs_dir) / f"{solver_name}.log"

    # build a text header boundary for debugging
    header = (
        f"{'=' * 80}\n"
        f"[BENCHMARK] {benchmark_name}\n"
        f"[STATUS] {status} | [RUNTIME] {runtime}s | [EXIT CODE] {exit_code}\n"
        f"{'=' * 80}\n"
    )

    with open(log_file_path, "a") as f:
        if fcntl:
            fcntl.flock(f.fileno(), fcntl.LOCK_EX)
        try:
            f.write(header)
            f.write(raw_output)
            f.write("\n\n")  # padding spacer between benchmark blocks
        finally:
            if fcntl:
                fcntl.flock(f.fileno(), fcntl.LOCK_UN)


def run_single_instance(
    solver_name, solver_path, benchmark_path, timeout, evaluation_csv, logs_dir
):
    benchmark_abs = Path(benchmark_path).resolve()
    solver_abs = Path(solver_path).resolve()
    solver_dir = solver_abs.parent

    # baseline configuration structure to ensure alignment in CSV under any condition
    result_template = {
        "solver": solver_name,
        "benchmark": benchmark_abs.name,
        "status": "FAILED",
        "runtime_seconds": 0.0,
        "code": -1,
        "optimum_value": "",
    }

    with tempfile.TemporaryDirectory() as tmpdir:
        tmpdir_path = Path(tmpdir)
        try:
            # 1. link solver files
            for file_path in solver_dir.iterdir():
                if file_path.is_file():
                    (tmpdir_path / file_path.name).symlink_to(file_path)

            # 2. handle benchmark decompression dynamically inside the sandbox
            if benchmark_abs.suffix == ".xz":
                # create an uncompressed plain text clone name inside the sandbox
                local_benchmark = (
                    tmpdir_path / benchmark_abs.stem
                )  # drops the .xz extension
                print(f"[DECOMPRESSING] {benchmark_abs.name} into sandbox...")
                with lzma.open(benchmark_abs, "rb") as f_in:
                    with open(local_benchmark, "wb") as f_out:
                        f_out.write(f_in.read())
            else:
                # if it's already a raw .wcnf, create a direct symlink to it
                local_benchmark = tmpdir_path / benchmark_abs.name
                local_benchmark.symlink_to(benchmark_abs)

            local_solver_script = tmpdir_path / solver_abs.name

            # 3. hand the isolated uncompressed file path to the execution matrix
            cmd = [str(local_solver_script), str(local_benchmark)]

            print(f"[STARTING] {solver_name} on {benchmark_abs.name}")

            start_time = time.perf_counter()
            result = subprocess.run(
                cmd,
                cwd=tmpdir,
                capture_output=True,
                text=True,
                errors="backslashreplace",
                timeout=timeout + 5,
            )
            elapsed_time = time.perf_counter() - start_time
            exit_code = result.returncode
            runtime_rounded = round(elapsed_time, 3)

            # parse standard maxsat execution statuses
            full_output = result.stdout + "\n" + result.stderr

            optimum_val = ""

            # strict binary evaluation
            if "s OPTIMUM FOUND" in full_output:
                parsed_val = parse_optimum_value(full_output)
                if parsed_val is not None:
                    status = "OPTIMUM"
                    optimum_val = parsed_val
                else:
                    status = "ERROR_PARSING_OPTIMUM"
                    print(
                        f"[PARSING ERROR] Solver {solver_name} found optimum, but regex extraction failed!"
                    )
            else:
                status = "FAILED"

            print(
                f"[FINISHED] {solver_name} on {benchmark_abs.name} ({runtime_rounded}s, Code: {exit_code})"
            )

            result_template.update(
                {
                    "status": status,
                    "runtime_seconds": runtime_rounded,
                    "code": exit_code,
                    "optimum_value": optimum_val,
                }
            )

            append_text_log_atomic(
                solver_name,
                benchmark_abs.name,
                status,
                runtime_rounded,
                exit_code,
                full_output,
                logs_dir,
            )

        except subprocess.TimeoutExpired:
            print(f"[TIMEOUT] {solver_name} on {benchmark_abs.name} (>{timeout}s)")
            result_template.update(
                {
                    "status": "TIMEOUT",
                    "runtime_seconds": float(timeout),
                    "code": -1,
                    "optimum_value": "",
                }
            )
            append_text_log_atomic(
                solver_name,
                benchmark_abs.name,
                "TIMEOUT",
                timeout,
                -1,
                f"Execution timed out past hard ceiling limit of {timeout} seconds.",
                logs_dir,
            )

        except Exception as e:
            print(f"[ERROR] {solver_name} on {benchmark_abs.name}: {str(e)}")
            result_template.update(
                {
                    "status": "ERROR",
                    "runtime_seconds": 0.0,
                    "code": -1,
                    "optimum_value": "",
                }
            )
            append_text_log_atomic(
                solver_name,
                benchmark_abs.name,
                "ERROR",
                0.0,
                -1,
                f"Internal wrapper runner failure exception:\n{str(e)}",
                logs_dir,
            )

        finally:
            append_row_atomic(result_template, evaluation_csv)


def main():
    config = load_config()
    timeout = config.get("timeout_seconds", 1200)

    if len(sys.argv) > 2:
        run_timestamp = sys.argv[2]
    else:
        run_timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

    base_result_dir = Path(config.get("result_dir", "./results"))
    active_run_dir = base_result_dir / f"eval_{run_timestamp}"
    logs_dir = active_run_dir / "logs"

    active_run_dir.mkdir(parents=True, exist_ok=True)
    logs_dir.mkdir(parents=True, exist_ok=True)

    evaluation_csv = active_run_dir / "evaluation_results.csv"

    benchmark_files = []
    for b_dir in config.get("benchmark_dirs", []):
        path = Path(b_dir)
        if path.exists():
            benchmark_files.extend(
                list(path.glob("*.wcnf")) + list(path.glob("*.wcnf.xz"))
            )
    benchmark_files.sort()

    solver_keys = sorted(list(config.get("solvers", {}).keys()))
    solvers_dict = config.get("solvers", {})

    all_tasks = []
    for s_key in solver_keys:
        for b_file in benchmark_files:
            all_tasks.append(
                (
                    s_key,
                    solvers_dict[s_key],
                    b_file,
                    timeout,
                    str(evaluation_csv),
                    str(logs_dir),
                )
            )

    if len(sys.argv) > 1:
        try:
            task_idx = int(sys.argv[1])
            if 0 <= task_idx < len(all_tasks):
                target_task = all_tasks[task_idx]
                print(
                    f"[Slurm Node Task {task_idx}] Assigned to target directory: eval_{run_timestamp}"
                )
                run_single_instance(*target_task)
            else:
                print(
                    f"Error: Slurm environment array allocation index {task_idx} out of bounds."
                )
                sys.exit(1)
        except ValueError:
            print(
                "Invalid initialization index format passed. Reverting to local execution routing."
            )
            sys.exit(1)
    else:
        max_workers = config.get("max_workers", 1)
        print(
            f"Initialized local runtime matrix environment. Output path: {active_run_dir}"
        )
        print(
            f"Loaded {len(solver_keys)} solver(s) and {len(benchmark_files)} benchmark(s)."
        )
        print(
            f"Total flattened executions mapped: {len(all_tasks)}. Running via {max_workers} threads.\n---"
        )

        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            futures = [
                executor.submit(run_single_instance, *task) for task in all_tasks
            ]
            for future in futures:
                future.result()

        print(
            f"\nLocal evaluation pipeline executed completely. Results at: {active_run_dir}"
        )


if __name__ == "__main__":
    main()
