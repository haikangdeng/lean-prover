#!/usr/bin/env python3
"""
Script to combine 100_subset_main.json and 100_subset_translations.json
into a single file 100_subset_full.json
"""

import json
from typing import Dict, List, Any

def load_json_file(filename: str) -> List[Dict[str, Any]]:
    """Load a JSON file and return the data."""
    try:
        with open(filename, 'r', encoding='utf-8') as f:
            return json.load(f)
    except FileNotFoundError:
        print(f"Error: File {filename} not found.")
        return []
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON in {filename}: {e}")
        return []

def create_lookup_dict(data: List[Dict[str, Any]]) -> Dict[tuple, Dict[str, Any]]:
    """Create a lookup dictionary using (source_idx, target_idx) as key."""
    lookup = {}
    for item in data:
        source_idx = item.get('source_idx')
        target_idx = item.get('target_idx')
        if source_idx is not None and target_idx is not None:
            lookup[(source_idx, target_idx)] = item
    return lookup

def combine_datasets(main_data: List[Dict[str, Any]], 
                    translations_data: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    """Combine the two datasets by matching source_idx and target_idx."""
    
    # Create lookup dictionary for translations
    translations_lookup = create_lookup_dict(translations_data)
    
    # Combine the datasets
    combined_data = []
    
    for item in main_data:
        source_idx = item.get('source_idx')
        target_idx = item.get('target_idx')
        
        if source_idx is not None and target_idx is not None:
            key = (source_idx, target_idx)
            
            # Create a copy of the main item
            combined_item = item.copy()
            
            # Add NL_problem_statement if available
            if key in translations_lookup:
                combined_item['NL_problem_statement'] = translations_lookup[key].get('NL_problem_statement', '')
            else:
                combined_item['NL_problem_statement'] = ''
            
            combined_data.append(combined_item)
        else:
            # If no source_idx or target_idx, add as is
            combined_data.append(item)
    
    return combined_data

def save_json_file(data: List[Dict[str, Any]], filename: str) -> bool:
    """Save data to a JSON file."""
    try:
        with open(filename, 'w', encoding='utf-8') as f:
            json.dump(data, f, indent=4, ensure_ascii=False)
        return True
    except Exception as e:
        print(f"Error saving {filename}: {e}")
        return False

def main():
    """Main function to combine the datasets."""
    
    # Load the datasets
    print("Loading 100_subset_main.json...")
    main_data = load_json_file('100_subset_main.json')
    
    print("Loading 100_subset_translations.json...")
    translations_data = load_json_file('100_subset_translations.json')
    
    if not main_data:
        print("Error: Could not load main dataset.")
        return
    
    if not translations_data:
        print("Error: Could not load translations dataset.")
        return
    
    print(f"Loaded {len(main_data)} items from main dataset")
    print(f"Loaded {len(translations_data)} items from translations dataset")
    
    # Combine the datasets
    print("Combining datasets...")
    combined_data = combine_datasets(main_data, translations_data)
    
    print(f"Combined dataset has {len(combined_data)} items")
    
    # Save the combined dataset
    print("Saving combined dataset to 100_subset_full.json...")
    if save_json_file(combined_data, '100_subset_full.json'):
        print("Successfully saved 100_subset_full.json")
        
        # Print some statistics
        nl_statements_count = sum(1 for item in combined_data if item.get('NL_problem_statement'))
        print(f"Items with NL problem statements: {nl_statements_count}/{len(combined_data)}")
    else:
        print("Failed to save combined dataset.")

if __name__ == "__main__":
    main() 