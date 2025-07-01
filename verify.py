import subprocess
import os
from tqdm.auto import tqdm
import json
import argparse

def main(args):

    lines = []

    for file in tqdm(sorted(os.listdir(args.output_dir))):
        if file.endswith(".lean"):
            file_path = os.path.join(args.output_dir, file)
            process = subprocess.run(["lake", "env", "lean", file_path], 
                                    cwd=args.lean_dir, 
                                    capture_output=True, 
                                    text=True)
            
            # TODO: check if placeholders (e.g. sorry) are in code
            # TODO: check if the proven theorem is the exact theorem in the problem statement
            
            if process.returncode == 0:
                print("Lean code verification successful!")
            else:
                print("Lean code verification failed.")
                print(process.stderr)
            line = {
                "edge": os.path.basename(file),
                "correct": process.returncode == 0,
                "stdout": process.stdout,
            }
            lines.append(line)
    
    with open(os.path.join(args.output_dir, "_verification_results.jsonl"), "w") as f:
        for line in lines:
            json_line = json.dumps(line)
            f.write(f"{json_line}\n")


def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lean_dir", type=str, default="/data2/haikang/projects/lean-prover/lean-project")
    parser.add_argument("--output_dir", type=str, default="/data2/haikang/projects/lean-prover/output/o3-mini",
                        help="Directory containing the generated Lean files.")
    return parser.parse_args()


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    args = parse_args()
    main(args)