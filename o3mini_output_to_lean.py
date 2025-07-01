import os
import json

def clean_and_write_lean(json_file_path):
    
    with open(json_file_path, 'r', encoding='utf-8') as f:
        data = json.load(f)

    response_text = data["response"]
    lines = response_text.splitlines()
    
    start_index = -1
    end_index = -1

    # 1. Find the starting line index by finding the first line that starts with "import"
    for i, line in enumerate(lines):
        if line.strip().startswith("import"):
            start_index = i
            break  # Found the start, stop searching

    if start_index == -1:
        print(f"Warning: No 'import' statement found in {json_file_path}. Cannot extract code.")
        return

    # 2. Find the ending line index by checking for multiple separator patterns
    # Start searching from the line immediately after the code starts
    for i in range(start_index + 1, len(lines)):
        stripped_line = lines[i].strip()

        # Pattern 1: Hyphen separator (e.g., '---')
        is_hyphen_sep = len(stripped_line) >= 3 and all(c == '-' for c in stripped_line)

        # Pattern 2: Box-drawing separator (e.g., '───')
        is_box_sep = len(stripped_line) >= 3 and all(c == '─' for c in stripped_line)

        # Pattern 3: Text-based separator (e.g., '––– Code End –––')
        is_text_sep = "Code End" in lines[i]

        if is_hyphen_sep or is_box_sep or is_text_sep:
            end_index = i
            break # Found the first separator, stop searching

    # 3. Extract the code lines based on found indices
    if end_index != -1:
        # A separator was found, so the code is between start and end
        code_lines = lines[start_index:end_index]
    else:
        # No separator was found, so assume the code runs to the end of the response
        code_lines = lines[start_index:]

    cleaned_code = "\n".join(code_lines).strip()

    if not cleaned_code:
        print(f"Warning: Found an import but extracted empty code from {json_file_path}.")
        return

    # 4. Write the cleaned code to a new .lean file
    base_name = os.path.splitext(json_file_path)[0]
    lean_file_path = f"{base_name}.lean"
    
    try:
        with open(lean_file_path, 'w', encoding='utf-8') as lean_file:
            lean_file.write(cleaned_code)
        print(f"Successfully processed {os.path.basename(json_file_path)} -> {os.path.basename(lean_file_path)}")
    except IOError as e:
        print(f"Error writing to file {lean_file_path}: {e}")


def main():
    """
    Main function to find and process all .json files in the current directory.
    """
    directory = os.path.dirname(os.path.abspath(__file__))
    print(f"Searching for .json files in: {directory}")
    
    found_files = False
    for filename in os.listdir(directory):
        if filename.endswith(".json"):
            found_files = True
            json_file_path = os.path.join(directory, filename)
            clean_and_write_lean(json_file_path)
            
    if not found_files:
        print("No .json files found in this directory.")


if __name__ == "__main__":
    main()