# generate the unique timestamp once
TS=$(date +%Y%m%d_%H%M%S)

# force creation of the directory BEFORE Slurm looks for it
mkdir -p "logs/${TS}"

# launch sbatch, feeding the exact paths dynamically
sbatch \
  --output="logs/${TS}/maxsat_%A_%a.out" \
  --error="logs/${TS}/maxsat_%A_%a.err" \
  --export=ALL,RUN_TIMESTAMP="${TS}" \
  submit_eval.sbatch