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
    
    with open("100_edges.json", "r") as f:
        edges = json.load(f)

    # Create output directory structure once
    style = "end2end"
    if args.informal2formal:
        style = "informal2formal"
    else:
        style = style + "_" + args.reasoning
    output_dir = os.path.join(args.output_dir, args.model, style)
    os.makedirs(output_dir, exist_ok=True)

    for i, (source_idx, target_idx) in enumerate(tqdm(edges[:args.num_examples])):
    # for i in tqdm(range(args.num_examples)):
    #     source_idx, target_idx = 0, 0
    #     while source_idx == target_idx:
    #         source_idx = torch.randint(0, len(theorem_generator.equations), (1,)).item()
    #         target_idx = torch.randint(0, len(theorem_generator.equations), (1,)).item()

        statement = theorem_generator.prepare_statement(source_idx=source_idx, target_idx=target_idx)
        format_type = "informal2formal" if args.informal2formal else "default"
        prompt = format_prompt(statement, format_type=format_type)

        output = client.responses.create(
            model=args.model,
            instructions="You are a helpful assistant.",
            input=prompt,
            reasoning={"effort": args.reasoning}
            # temperature=0   # for greedy decoding
        )

        response = output.output_text
        
        implies_or_not = "implies" if "true" in theorem_generator.implications[source_idx][target_idx] else "not_implies"
        response_file_name = f"Equation{source_idx + 1}_{implies_or_not}_Equation{target_idx + 1}.json"
        response_file_name = os.path.join(output_dir, response_file_name)

        with open(response_file_name, "w") as f:
            json.dump({
                "statement": statement,
                "response": response,
            }, f, indent=4, ensure_ascii=False)

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
    parser.add_argument("--model", type=str, default="o3", choices=["o3-mini", "o3"])
    parser.add_argument("--reasoning", type=str, default="medium", choices=["low", "medium", "high"])
    parser.add_argument("--output_dir", type=str, default="output")
    parser.add_argument("--informal2formal", action="store_true", help="Whether to use informal-to-formal prompting")

    return parser.parse_args()

if __name__ == "__main__":
    args = parse_args()
    main(args)