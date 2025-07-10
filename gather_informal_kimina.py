import json
import os
import sys
import argparse
import re


def remove_think_prefix(response):
    # Remove '<think>\n:' if it exists at the beginning
    if isinstance(response, str):
        response = re.sub(r'^<think>\n:', '', response)
    return response


def remove_after_tactics(response):
    if not isinstance(response, str):
        return response
    # Remove everything after the first '```tactics'
    idx = response.find('```tactics')
    if idx != -1:
        response = response[:idx]
    return response


def remove_last_sentence(text):
    # Remove trailing whitespace/newlines
    text = text.rstrip('\n')
    # Find the last sentence-ending punctuation
    # Acceptable sentence endings: '.', '!', '?'
    # We'll use regex to split into sentences
    sentences = re.split(r'(?<=[.!?])\s+', text.strip())
    if len(sentences) > 1:
        # Remove the last sentence
        text = ' '.join(sentences[:-1])
    else:
        text = ''
    return text.strip()


def parse_kimina_response(response):
    response = remove_think_prefix(response)
    response = remove_after_tactics(response)
    response = remove_last_sentence(response)
    return response


def main():
    parser = argparse.ArgumentParser(description='Process informal test or valid data with kimina outputs.')
    parser.add_argument('--split', choices=['test', 'valid'], default='test', help='Which data split to process (test or valid)')
    args = parser.parse_args()

    if args.split == 'test':
        input_file = 'informal_test.jsonl'
        output_file = 'informal_test_kimina.jsonl'
        model_dir = 'output_informal/kimina/test'
    else:
        input_file = 'informal_valid.jsonl'
        output_file = 'informal_valid_kimina.jsonl'
        model_dir = 'output_informal/kimina/valid'

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
                                data['response'] = parse_kimina_response(response)
                        except Exception:
                            pass
                fout.write(json.dumps(data, ensure_ascii=False) + '\n')
            except Exception:
                continue

if __name__ == '__main__':
    main() 