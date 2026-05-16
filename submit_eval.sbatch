#!/bin/bash -l
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=1
#SBATCH --time=24:00:00
#SBATCH --job-name=mse2024_eval
# keep a master fallback log so Slurm is happy at startup
#SBATCH --output=logs/slurm_master_%A_%a.out
#SBATCH --error=logs/slurm_master_%A_%a.err
# CRITICAL SETTING: 
# Set the array boundary size to match exactly: (Total Solvers * Total Benchmarks) - 1
# e.g., if you have 2 solvers and 250 benchmarks, total tasks = 500, use: --array=0-499%50
#SBATCH --array=0-19%20

# load the module
module add python/3.12-conda

# activate conda env
conda activate mse24env

# enforce strict script execution rules
set -euo pipefail
export OMP_NUM_THREADS=$SLURM_CPUS_PER_TASK
export SRUN_CPUS_PER_TASK=$SLURM_CPUS_PER_TASK

# create a folder for standard Slurm out/err reports
LOG_DIR="logs/${RUN_TIMESTAMP}"
mkdir -p "$LOG_DIR"

# >>> redirect stdout/stderr from this point forward
exec > "${LOG_DIR}/maxsat_${SLURM_ARRAY_JOB_ID}_${SLURM_ARRAY_TASK_ID}.out"
exec 2> "${LOG_DIR}/maxsat_${SLURM_ARRAY_JOB_ID}_${SLURM_ARRAY_TASK_ID}.err"

echo "[$(date)] Slurm Master Job Matrix Initialized: ID=$SLURM_JOB_ID | Array_ID=$SLURM_ARRAY_TASK_ID"
echo "Targeting global output folder context: eval_${RUN_TIMESTAMP}"

# pass the dynamic array ID ($1) and the locked timestamp ($2).
python3 run_eval.py "$SLURM_ARRAY_TASK_ID" "$RUN_TIMESTAMP"

echo "[$(date)] Slurm Node Array Instance $SLURM_ARRAY_TASK_ID complete."
