#!/usr/bin/env python3
import json
import os
import re
from pathlib import Path

def extract_response_content(file_path):
    """Extract response content from a file, taking everything before the sentence before '```lean'"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
            data = json.loads(content)
            response = data.get('response', '')
        
        # Find the position of "```lean"
        lean_start = response.find('```lean')
        if lean_start != -1:
            # Find the last sentence before "```lean"
            # Look for the last period, exclamation mark, or question mark before "```lean"
            before_lean = response[:lean_start]
            
            # Find the last sentence boundary
            last_sentence_end = -1
            for i in range(len(before_lean) - 1, -1, -1):
                if before_lean[i] in '.!?':
                    last_sentence_end = i
                    break
            
            if last_sentence_end != -1:
                # Take everything up to the last sentence boundary
                return before_lean[:last_sentence_end + 1].strip()
            else:
                # No sentence boundary found, take everything before "```lean"
                return before_lean.strip()
        else:
            return response.strip()
            
    except FileNotFoundError:
        print(f"Warning: File not found: {file_path}")
        return ''
    except Exception as e:
        print(f"Warning: Error reading {file_path}: {e}")
        return ''

def determine_file_name(source_idx, target_idx, problem_statement):
    """Determine the correct file name based on source_idx, target_idx, and problem_statement"""
    source_eq = source_idx + 1
    target_eq = target_idx + 1
    
    # Check if the problem statement contains "implies" or "not_implies"
    if "implies" in problem_statement and "not_implies" not in problem_statement:
        # This is an "implies" case
        return f"Equation{source_eq}_implies_Equation{target_eq}"
    else:
        # This is a "not_implies" case
        return f"Equation{source_eq}_not_implies_Equation{target_eq}"

def main():
    # Read the existing full JSON file
    with open('100_subset_full.json', 'r', encoding='utf-8') as f:
        full_data = json.load(f)
    
    # Directory containing the informal2formal files
    informal2formal_dir = Path('output/o3/informal2formal')
    
    processed_count = 0
    found_count = 0
    
    for record in full_data:
        source_idx = record['source_idx']
        target_idx = record['target_idx']
        problem_statement = record['problem_statement']
        
        # Determine the base file name
        base_name = determine_file_name(source_idx, target_idx, problem_statement)
        
        # Try to find the file (could be .json or .lean)
        json_file = informal2formal_dir / f"{base_name}.json"
        
        response_content = ''
        file_found = False
        
        # Try JSON file first
        if json_file.exists():
            response_content = extract_response_content(json_file)
            file_found = True
            file_type = 'json'
        
        # Find the corresponding record in full_data and add the o3_informal_proof
        for full_record in full_data:
            if (full_record.get('source_idx') == source_idx and 
                full_record.get('target_idx') == target_idx):
                
                # Add the o3_informal_proof field
                full_record['o3_informal_proof'] = response_content
                processed_count += 1
                
                # Print progress
                if file_found:
                    print(f"✓ Found {base_name}.{file_type} -> added to full data")
                    found_count += 1
                else:
                    print(f"✗ Missing: {base_name} -> added empty field")
                break
        
        # Print progress
        if not file_found:
            print(f"✗ Missing: {base_name}")
    
    # Save the updated full data back to the file
    with open('100_subset_full.json', 'w', encoding='utf-8') as f:
        json.dump(full_data, f, indent=2, ensure_ascii=False)
    
    # Print summary
    total_count = len(full_data)
    
    print(f"\nSummary:")
    print(f"Total records processed: {processed_count}")
    print(f"Files found: {found_count}")
    print(f"Files missing: {total_count - found_count}")
    print(f"Updated: 100_subset_full.json")
    
    # Print some examples of extracted content
    print(f"\nExample extracted content (first 3 found files):")
    count = 0
    for record in full_data:
        if 'o3_informal_proof' in record and record['o3_informal_proof'] and count < 3:
            print(f"\n--- {record.get('source_idx', 'N/A')} -> {record.get('target_idx', 'N/A')} ---")
            content = record['o3_informal_proof']
            if len(content) > 200:
                print(content[:200] + "...")
            else:
                print(content)
            count += 1

if __name__ == "__main__":
    main() 