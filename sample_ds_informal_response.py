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
        
        prompt = format_prompt(formal_statement, format_type="informal_ds")
        # print(prompt)

        chat = [
            {"role": "user", "content": prompt},
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
        
        print(f"Sample {i + 1}:\n{response}\n")
        
        # Use the problem name for the output file
        problem_name = example.get("problem_name", f"example_{i+1}")
        response_file_name = os.path.join(args.output_dir, args.split, problem_name)
        
        with open(response_file_name + ".json", "w") as f:
            json.dump({ 
                "statement": formal_statement,
                "response": response,
            }, f, indent=4, ensure_ascii=False)
            
            

def parse_args():
    parser = argparse.ArgumentParser()
    # parser.add_argument("--num_examples", type=int, default=100, help="Number of examples to generate")
    parser.add_argument("--max_new_tokens", type=int, default=8192)
    # parser.add_argument("--cot", action="store_true", help="Whether to use chain-of-thought prompting")
    parser.add_argument("--output_dir", type=str, default="output_informal/ds")
    # parser.add_argument("--informal2formal", action="store_true", help="Whether to use informal-to-formal prompting")
    parser.add_argument("--split", type=str, default="test", choices=["test", "valid"], help="Which split to use: 'test' or 'valid'")
    return parser.parse_args()

if __name__ == "__main__":
    args = parse_args()
    main(args)