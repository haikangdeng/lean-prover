from transformers import AutoModelForCausalLM, AutoTokenizer, set_seed
import torch
from utils import get_theorem_generator, format_prompt
import argparse
from tqdm.auto import tqdm
import os
import json

set_seed(42)

def main(args):
    model_id = "deepseek-ai/DeepSeek-Prover-V2-7B"  # or deepseek-ai/DeepSeek-Prover-V2-671B

    tokenizer = AutoTokenizer.from_pretrained(model_id)
    model = AutoModelForCausalLM.from_pretrained(
        model_id, 
        device_map="auto", 
        torch_dtype=torch.bfloat16, 
        trust_remote_code=True
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

        chat = [
            {"role": "user", "content": prompt},
        ]
        inputs = tokenizer.apply_chat_template(chat, tokenize=True, add_generation_prompt=True, return_tensors="pt").to(model.device)

        outputs = model.generate(
            inputs,
            max_new_tokens=args.max_new_tokens,
            return_dict_in_generate=True,
            pad_token_id=tokenizer.eos_token_id,
        )

        input_length = inputs.shape[1]
        response = tokenizer.decode(outputs.sequences[0][input_length:], skip_special_tokens=True)

        # parse the last ```lean4 ... ``` block
        lean_response = response.split("```lean4")[-1].split("```")[0].strip()
        statement_prefix = statement.split("theorem")[0].strip()
        full_lean_response = statement_prefix + "\n\n" + lean_response
        
        print(f"Sample {i + 1}:\n{full_lean_response}\n")
        
        implies_or_not = "implies" if "true" in theorem_generator.implications[source_idx][target_idx] else "not_implies"
        response_file_name = f"Equation{source_idx + 1}_{implies_or_not}_Equation{target_idx + 1}"
        # cot_path = "cot" if args.cot else "no_cot"
        # response_file_name = os.path.join(args.output_dir, cot_path, response_file_name)
        response_file_name = os.path.join(args.output_dir, response_file_name)
        
        with open(response_file_name + ".lean", "w") as f:
            f.write(full_lean_response)
        with open(response_file_name + ".json", "w") as f:
            json.dump({
                "statement": statement,
                "response": response,
            }, f)
            
            

def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("--num_examples", type=int, default=100, help="Number of examples to generate")
    parser.add_argument("--max_new_tokens", type=int, default=8192)
    parser.add_argument("--cot", action="store_true", help="Whether to use chain-of-thought prompting")
    parser.add_argument("--output_dir", type=str, default="output/ds")
    return parser.parse_args()

if __name__ == "__main__":
    args = parse_args()
    main(args)