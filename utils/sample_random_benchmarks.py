import random
import shutil
from pathlib import Path

# configuration
INPUT_DIR = "benchmarks-mse24/mse24-exact-weighted/"
SEED_VALUE = 42  # Change this to any number you want
SAMPLE_SIZE = 50

# set the seed for reproducibility
random.seed(SEED_VALUE)

#  paths
input_path = Path(INPUT_DIR)
# get the parent directory (e.g., "benchmarks-mse24")
parent_path = input_path.parent
output_path = parent_path / "random-50-benchmarks"

# get all files in the input directory (files only, no subfolders)
all_files = [f for f in input_path.iterdir() if f.is_file()]

# ensure there are enough files to sample from
if len(all_files) < SAMPLE_SIZE:
    print(f"Warning: Only found {len(all_files)} files. Sampling all of them.")
    sampled_files = all_files
else:
    # select 50 random files cleanly and reproducibly
    sampled_files = random.sample(all_files, SAMPLE_SIZE)

# new output folder
output_path.mkdir(parents=True, exist_ok=True)

# copy the selected files
print(f"Copying {len(sampled_files)} files to {output_path}...")
for file_path in sampled_files:
    shutil.copy(file_path, output_path / file_path.name)

print("Completed!")
