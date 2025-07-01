from transformers import AutoModelForCausalLM, AutoTokenizer, set_seed
import torch
from utils import get_theorem_generator, format_prompt
import argparse
from tqdm.auto import tqdm
import os
import json

set_seed(42)

def main():
    lines = []
    theorem_generator = get_theorem_generator()

    with open("100_edges.json", "r") as f:
        edges = json.load(f)

    for i, (source_idx, target_idx) in enumerate(tqdm(edges[:100])):
    # for i in tqdm(range(args.num_examples)):
    #     source_idx, target_idx = 0, 0
    #     while source_idx == target_idx:
    #         source_idx = torch.randint(0, len(theorem_generator.equations), (1,)).item()
    #         target_idx = torch.randint(0, len(theorem_generator.equations), (1,)).item()

        source_equation = theorem_generator.equations[source_idx]
        target_equation = theorem_generator.equations[target_idx]
        
        converted_source_equation = theorem_generator._convert_equation(source_equation)
        converted_target_equation = theorem_generator._convert_equation(target_equation)

        statement = theorem_generator.prepare_statement(source_idx=source_idx, target_idx=target_idx)
        prompt_end2end = format_prompt(statement, cot=False, informal2formal=False)
        prompt_cot = format_prompt(statement, cot=True, informal2formal=False)

        line = {
            "source_idx": source_idx,
            "target_idx": target_idx,
            "source_equation": source_equation,
            "target_equation": target_equation,
            "converted_source_equation": converted_source_equation,
            "converted_target_equation": converted_target_equation,
            "problem_statement": statement,
            "prompt_end2end": prompt_end2end,
            "prompt_cot": prompt_cot,
        }
        lines.append(line)
        
    with open("100_subset.json", 'w') as f:
        json.dump(lines, f, indent=4, ensure_ascii=False)

if __name__ == "__main__":
    main()