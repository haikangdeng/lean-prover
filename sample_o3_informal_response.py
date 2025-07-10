from transformers import AutoModelForCausalLM, AutoTokenizer
from transformers.trainer_utils import set_seed
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
    
    # Select the appropriate file based on the split argument
    if args.split == "test":
        data_file = "informal_test.jsonl"
    elif args.split == "valid":
        data_file = "informal_valid.jsonl"
    else:
        raise ValueError("--split must be 'test' or 'valid'")

    # Read the data from the selected file
    examples = []
    with open(data_file, 'r') as f:
        for line in f:
            line = line.strip()
            if line:
                examples.append(json.loads(line))

    for i, example in enumerate(tqdm(examples)):
        problem_name = example["problem_name"]
        informal_statement = example["input_informal"]
        formal_statement = example["input_formal_with_header"]
        
        prompt = format_prompt(formal_statement, format_type="informal_o3")

        output = client.responses.create(
            model=args.model,
            instructions="You are a helpful assistant.",
            input=prompt,
            # temperature=0   # for greedy decoding
        )

        response = output.output_text
        
        # Use the problem name for the output file
        problem_name = example.get("problem_name", f"example_{i+1}")
        response_file_name = os.path.join(args.output_dir, args.model, args.split, problem_name)
        
        with open(response_file_name + ".json", "w") as f:
            json.dump({ 
                "statement": formal_statement,
                "response": response,
            }, f, indent=4, ensure_ascii=False)
        
        print(f"Sample {i + 1}:\n{response}\n")


def parse_args():
    parser = argparse.ArgumentParser()
    # parser.add_argument("--max_new_tokens", type=int, default=8192)
    parser.add_argument("--output_dir", type=str, default="output_informal/")
    parser.add_argument("--model", type=str, default="o3", choices=["o3-mini", "o3"])
    parser.add_argument("--split", type=str, default="test", choices=["test", "valid"], help="Which split to use: 'test' or 'valid'")
    return parser.parse_args()

if __name__ == "__main__":
    args = parse_args()
    main(args) 