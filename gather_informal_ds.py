import json
import os
import sys
import argparse
import re


def extract_informal_proof(response):
    if not isinstance(response, str):
        return response
    # Find the section after '### Informal Proof' and before the next '###'
    match = re.search(r"### Informal Proof\s*(.*?)(?=^###|\Z)", response, re.DOTALL | re.MULTILINE)
    if match:
        return match.group(1).strip()
    return response


def main():
    parser = argparse.ArgumentParser(description='Process informal test or valid data with deepseek outputs.')
    parser.add_argument('--split', choices=['test', 'valid'], default='test', help='Which data split to process (test or valid)')
    args = parser.parse_args()

    if args.split == 'test':
        input_file = 'informal_test.jsonl'
        output_file = 'informal_test_ds.jsonl'
        model_dir = 'output_informal/ds/test'
    else:
        input_file = 'informal_valid.jsonl'
        output_file = 'informal_valid_ds.jsonl'
        model_dir = 'output_informal/ds/valid'

    with open(input_file, 'r', encoding='utf-8') as fin, open(output_file, 'w', encoding='utf-8') as fout:
        for line in fin:
            line = line.strip()
            if not line:
                continue
            try:
                data = json.loads(line)
                problem_name = data.get('problem_name')
                if problem_name:
                    model_path = os.path.join(model_dir, f'{problem_name}.json')
                    if os.path.exists(model_path):
                        try:
                            with open(model_path, 'r', encoding='utf-8') as modelf:
                                model_data = json.load(modelf)
                            response = model_data.get('response')
                            if response is not None:
                                data['response'] = extract_informal_proof(response)
                        except Exception:
                            pass
                fout.write(json.dumps(data, ensure_ascii=False) + '\n')
            except Exception:
                continue

if __name__ == '__main__':
    main() 