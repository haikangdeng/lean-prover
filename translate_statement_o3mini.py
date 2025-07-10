from transformers import AutoModelForCausalLM, AutoTokenizer, set_seed
import torch
from utils import get_theorem_generator
import argparse
from tqdm.auto import tqdm
import os
import json
from openai import OpenAI

set_seed(42)

def format_translation_prompt(statement: str):
    """
    Format a prompt asking O3-mini to translate a Lean problem to natural language.
    """
    prompt = """
Translate the following Lean 4 problem into a natural language problem. Output only the translated problem statement.
```lean4
{}
```
""".strip()
    return prompt.format(statement)

def main(args):
    
    with open("/data2/haikang/projects/openai_key.txt", "r") as f:
        api_key = f.read().strip()
        
    client = OpenAI(
        api_key = api_key
    )

    theorem_generator = get_theorem_generator()
    
    with open("100_edges.json", "r") as f:
        edges = json.load(f)

    # Initialize results list to store all translations
    results = []

    for i, (source_idx, target_idx) in enumerate(tqdm(edges[:args.num_examples])):
        statement = theorem_generator.prepare_statement(source_idx=source_idx, target_idx=target_idx)
        prompt = format_translation_prompt(statement)

        output = client.responses.create(
            model=args.model,
            instructions="You are a helpful assistant.",
            input=prompt,
            # temperature=0   # for greedy decoding
        )

        response = output.output_text
        
        # Add result to the list
        results.append({
            "source_idx": source_idx,
            "target_idx": target_idx,
            "NL_problem_statement": response
        })

        print(f"Sample {i + 1}:\n{response}\n")

    # Write all results to a single JSON file
    output_file = os.path.join(args.output_dir, f"100_subset_translations.json")
    # os.makedirs(args.output_dir, exist_ok=True)
    
    with open(output_file, "w") as f:
        json.dump(results, f, indent=4, ensure_ascii=False)
    
    print(f"All translations saved to: {output_file}")

def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--num_examples", type=int, default=100, help="Number of examples to translate")
    parser.add_argument("--model", type=str, default="o3-mini", choices=["o3-mini", "o3"])
    parser.add_argument("--output_dir", type=str, default=".")

    return parser.parse_args()

if __name__ == "__main__":
    args = parse_args()
    main(args)
