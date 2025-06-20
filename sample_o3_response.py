from transformers import AutoModelForCausalLM, AutoTokenizer, set_seed
import torch
from utils import get_theorem_generator, format_prompt
import argparse
from tqdm.auto import tqdm
import os
import json
from openai import OpenAI

set_seed(42)

def main(args):
    
    with open("/data2/haikang/projects/openai_key.txt", "r") as f:
        api_key = f.read().strip()
        
    client = OpenAI(
        api_key = api_key
    )

    theorem_generator = get_theorem_generator()
    
    # use tqdm to show progress
    for i in tqdm(range(args.num_examples)):
        source_idx, target_idx = 0, 0
        while source_idx == target_idx:
            source_idx = torch.randint(0, len(theorem_generator.equations), (1,)).item()
            target_idx = torch.randint(0, len(theorem_generator.equations), (1,)).item()

        statement = theorem_generator.prepare_statement(source_idx=source_idx, target_idx=target_idx)
        prompt = format_prompt(statement, cot=args.cot)

        output = client.responses.create(
            model=args.model,
            instructions="You are a helpful assistant.",
            input=prompt,
        )

        response = output.output_text
        
        implies_or_not = "implies" if "true" in theorem_generator.implications[source_idx][target_idx] else "not_implies"
        response_file_name = f"Equation{source_idx + 1}_{implies_or_not}_Equation{target_idx + 1}"
        # cot_path = "cot" if args.cot else "no_cot"
        # response_file_name = os.path.join(args.output_dir, cot_path, response_file_name)
        response_file_name = os.path.join(args.output_dir, args.model, response_file_name)

        with open(response_file_name + ".json", "w") as f:
            json.dump({
                "statement": statement,
                "response": response,
            }, f)

        # parse the last ```lean ... ``` block
        lean_response = response.split("```lean")[-1].split("```")[0].strip()
        # statement_prefix = statement.split("theorem")[0].strip()
        # if statement_prefix not in lean_response:
        #     lean_response = statement_prefix + "\n\n" + lean_response
        print(f"Sample {i + 1}:\n{lean_response}\n")

        with open(response_file_name + ".lean", "w") as f:
            f.write(lean_response)



def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--num_examples", type=int, default=100, help="Number of examples to generate")
    parser.add_argument("--cot", action="store_true", help="Whether to use chain-of-thought prompting")
    parser.add_argument("--model", type=str, default="o3-mini", choices=["o3-mini", "o3"])
    parser.add_argument("--output_dir", type=str, default="output")
    return parser.parse_args()

if __name__ == "__main__":
    args = parse_args()
    main(args)