from transformers import AutoModelForCausalLM, AutoTokenizer, set_seed
import torch
from utils import get_theorem_generator, format_prompt
import argparse
from tqdm.auto import tqdm
import os
import json

set_seed(42)

def main(args):
    model_id = "AI-MO/Kimina-Prover-Preview-Distill-7B"

    tokenizer = AutoTokenizer.from_pretrained(model_id)
    model = AutoModelForCausalLM.from_pretrained(
        model_id, 
        device_map="auto", 
        torch_dtype=torch.bfloat16, 
        trust_remote_code=True
    )

    theorem_generator = get_theorem_generator()
        
    with open("100_subset_full.json", "r") as f:
        full_data = json.load(f)

    for i, line in enumerate(tqdm(full_data[:args.num_examples])):
    # for i in tqdm(range(args.num_examples)):
    #     source_idx, target_idx = 0, 0
    #     while source_idx == target_idx:
    #         source_idx = torch.randint(0, len(theorem_generator.equations), (1,)).item()
    #         target_idx = torch.randint(0, len(theorem_generator.equations), (1,)).item()

        # statement = theorem_generator.prepare_statement(source_idx=source_idx, target_idx=target_idx)
        # formal_statement = format_prompt(statement, cot=args.cot, informal2formal=args.informal2formal)
        
        nl_problem_statement = line["NL_problem_statement"]
        lean_problem_statement = line["problem_statement"]
        
        
        # construct prompt with NL problem statement and Lean 4 formal statement
        prompt = "Think about and solve the following problem step by step in Lean 4."
        prompt += f"\n# Problem:{nl_problem_statement}"""
        prompt += f"\n# Formal statement:\n```lean4{lean_problem_statement}```\n"
        # prompt += f"\n# Formal statement:{formal_statement}\n"

        chat = [
            {"role": "system", "content": "You are an expert in mathematics and Lean 4."},
            {"role": "user", "content": prompt}
        ]
        inputs = tokenizer.apply_chat_template(chat, tokenize=True, add_generation_prompt=True, return_tensors="pt").to(model.device)

        with torch.inference_mode():
            outputs = model.generate(
                inputs,
                max_new_tokens=args.max_new_tokens,
                return_dict_in_generate=True,
                pad_token_id=tokenizer.eos_token_id,
            )

        input_length = inputs.shape[1]
        response = tokenizer.decode(outputs.sequences[0][input_length:], skip_special_tokens=True)

        # # parse the last ```lean4 ... ``` block
        # lean_response = response.split("```lean4")[-1].split("```")[0].strip()
        # statement_prefix = statement.split("theorem")[0].strip()
        # full_lean_response = statement_prefix + "\n\n" + lean_response
        
        print(f"Sample {i + 1}:\n{response}\n")
        
        # implies_or_not = "implies" if "true" in theorem_generator.implications[source_idx][target_idx] else "not_implies"
        implies_or_not = "not_implies" if "not_implies" in lean_problem_statement else "implies"
        source_idx = line["source_idx"]
        target_idx = line["target_idx"]
        response_file_name = f"Equation{source_idx + 1}_{implies_or_not}_Equation{target_idx + 1}"
        # cot_path = "cot" if args.cot else "no_cot"
        # response_file_name = os.path.join(args.output_dir, cot_path, response_file_name)
        response_file_name = os.path.join(args.output_dir, response_file_name)
        
        # with open(response_file_name + ".lean", "w") as f:
        #     f.write(full_lean_response)
        with open(response_file_name + ".json", "w") as f:
            json.dump({ 
                "statement": lean_problem_statement,
                "response": response,
            }, f, indent=4, ensure_ascii=False)
            
            

def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--num_examples", type=int, default=100, help="Number of examples to generate")
    parser.add_argument("--max_new_tokens", type=int, default=16384)
    # parser.add_argument("--cot", action="store_true", help="Whether to use chain-of-thought prompting")
    parser.add_argument("--output_dir", type=str, default="output/kimina")
    # parser.add_argument("--informal2formal", action="store_true", help="Whether to use informal-to-formal prompting")
    return parser.parse_args()

if __name__ == "__main__":
    args = parse_args()
    main(args)