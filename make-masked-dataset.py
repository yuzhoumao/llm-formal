import os
import argparse
import random

# Add a list of keywords to exclude from masking
EXCLUDE_KEYWORDS = ['EXTENDS']#, 'CONSTANTS', 'VARIABLES', 'ASSUME']

def mask_code_blocks(input_dir, masked_dir, blocks_to_mask):
    if not os.path.exists(masked_dir):
        os.makedirs(masked_dir)

    for protocol in os.listdir(input_dir):
        protocol_path = os.path.join(input_dir, protocol)
        if os.path.isdir(protocol_path):
            tla_file = os.path.join(protocol_path, f"{protocol}.tla")
            if os.path.isfile(tla_file):
                with open(tla_file, 'r') as file:
                    lines = file.readlines()

                masked_content = lines[:]
                code_blocks = []
                block_start = None
                in_comment_block = False
                in_code_block = False

                for i, line in enumerate(lines):
                    # Check for the start of a multiline comment block
                    if "(*" in line:
                        in_comment_block = True

                    # Check for the end of a multiline comment block
                    if "*)" in line and in_comment_block:
                        in_comment_block = False
                        continue

                    # Detect standalone comment line, not part of a comment block
                    standalone_comment = line.strip().startswith("\\*") and not in_comment_block

                    # Check if line contains excluded keywords
                    contains_exclude_keywords = any(keyword in line for keyword in EXCLUDE_KEYWORDS)

                    # Determine if this is the start of a new code block
                    if not in_comment_block and not standalone_comment and not contains_exclude_keywords and line.strip() and block_start is None:
                        block_start = i
                        in_code_block = True

                    # Determine if this is the end of a code block
                    if in_code_block and (standalone_comment or not line.strip() or "(*" in line):
                        in_code_block = False
                        code_blocks.append((block_start, i - 1))
                        block_start = None

                # If the last line of the file is part of a code block, close that block
                if in_code_block:
                    code_blocks.append((block_start, len(lines) - 1))

                # Choose random code blocks to mask, not exceeding the specified number
                blocks_to_mask = min(blocks_to_mask, len(code_blocks))
                blocks_chosen_to_mask = random.sample(code_blocks, blocks_to_mask) if code_blocks else []

                # Apply masking to the chosen blocks, avoiding lines with excluded keywords
                for start, end in blocks_chosen_to_mask:
                    for j in range(start, end + 1):
                        if not any(keyword in masked_content[j] for keyword in EXCLUDE_KEYWORDS):
                            masked_content[j] = ""  # Clear the line

                    # Insert the "MASKED CODE" tag if the entire block has been cleared
                    if start < len(masked_content) and not any(masked_content[j].strip() for j in range(start, end + 1)):
                        masked_content[start] = "(* MASKED CODE *)\n"

                # Write the masked content to a new file
                masked_file_path = os.path.join(masked_dir, f"{protocol}_MASKED.tla")
                with open(masked_file_path, 'w') as masked_file:
                    masked_file.writelines(masked_content)


def main():
    parser = argparse.ArgumentParser(description='Mask code blocks in TLA+ specification files.')
    parser.add_argument('-i', '--input_dir', required=True, help='Input directory with TLA files.')
    parser.add_argument('-m', '--masked_dir', required=True, help='Output directory for masked TLA files.')
    parser.add_argument('-b', '--blocks_to_mask', type=int, default=1, help='Number of code blocks to mask per file.')

    args = parser.parse_args()

    mask_code_blocks(args.input_dir, args.masked_dir, args.blocks_to_mask)

if __name__ == "__main__":
    main()
