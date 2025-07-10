import json
import os
import sys
import argparse

def main():
    parser = argparse.ArgumentParser(description='Process informal test or valid data with o3 or o3-mini outputs.')
    parser.add_argument('--split', choices=['test', 'valid'], default='test', help='Which data split to process (test or valid)')
    parser.add_argument('--model', choices=['o3', 'o3-mini'], default='o3', help='Which model outputs to use (o3 or o3-mini)')
    args = parser.parse_args()

    if args.split == 'test':
        input_file = 'informal_test.jsonl'
        if args.model == 'o3':
            output_file = 'informal_test_o3.jsonl'
            model_dir = 'output_informal/o3/test'
        else:
            output_file = 'informal_test_o3-mini.jsonl'
            model_dir = 'output_informal/o3-mini/test'
    else:
        input_file = 'informal_valid.jsonl'
        if args.model == 'o3':
            output_file = 'informal_valid_o3.jsonl'
            model_dir = 'output_informal/o3/valid'
        else:
            output_file = 'informal_valid_o3-mini.jsonl'
            model_dir = 'output_informal/o3-mini/valid'

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
                                data['response'] = response
                        except Exception:
                            pass
                fout.write(json.dumps(data, ensure_ascii=False) + '\n')
            except Exception:
                continue

if __name__ == '__main__':
    main() 