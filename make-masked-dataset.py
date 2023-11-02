import os
import argparse
import random

def mask_code_blocks(input_dir, masked_dir, blocks_to_mask):
    if not os.path.exists(masked_dir):
        os.makedirs(masked_dir)

    for protocol in os.listdir(input_dir):
        protocol_path = os.path.join(input_dir, protocol)
        if os.path.isdir(protocol_path):
            tla_file = os.path.join(protocol_path, f"{protocol}.tla")
            if os.path.isfile(tla_file):
                with open(tla_file, 'r') as file:
                    content = file.readlines()

                code_blocks = []
                in_comment_block = False
                in_keyword_block = False
                skip_keywords = ['EXTENDS', 'CONSTANTS', 'VARIABLES', 'ASSUME']
                code_block_start_idx = None

                # Identify code blocks
                for i, line in enumerate(content):
                    if any(line.strip().startswith(kw) for kw in skip_keywords):
                        in_keyword_block = True
                    elif not line.strip().startswith("    ") and in_keyword_block:
                        in_keyword_block = False

                    if line.strip().startswith("(*") or line.strip().startswith("\\*"):
                        if in_comment_block:  # End of comment block
                            in_comment_block = False
                        else:  # Start of comment block
                            in_comment_block = True
                            # If we were in a code block, end it before the comment
                            if code_block_start_idx is not None:
                                code_blocks.append((code_block_start_idx, i - 1))
                                code_block_start_idx = None
                        continue

                    if in_comment_block or in_keyword_block or line.strip() == "":
                        continue

                    if code_block_start_idx is None:
                        code_block_start_idx = i
                    elif (i == len(content) - 1 or content[i + 1].strip() == "" or in_comment_block or in_keyword_block or any(content[i + 1].strip().startswith(kw) for kw in skip_keywords)):
                        if code_block_start_idx != i:  # Check to avoid single-line/masked blank lines
                            code_blocks.append((code_block_start_idx, i))
                        code_block_start_idx = None

                # Randomly select blocks to mask
                blocks_to_mask_indices = random.sample(code_blocks, min(blocks_to_mask, len(code_blocks)))

                masked_content = content[:1]  # Start with the first line unmasked

                # Track whether we've inserted the masked code comment
                inserted_mask_comment = False
                for i, line in enumerate(content[1:], 1):
                    if any(start <= i <= end for start, end in blocks_to_mask_indices) and line.strip() != "":
                        if not inserted_mask_comment:
                            # Insert the masked code comment once at the beginning of the block
                            masked_content.append("(* MASKED CODE *)\n")
                            inserted_mask_comment = True
                    else:
                        # If the line is not in a masked block, add it to the output and reset the comment flag
                        masked_content.append(line)
                        inserted_mask_comment = False

                # Write the masked content to a new file
                masked_file_path = os.path.join(masked_dir, f"{protocol}_MASKED.tla")
                with open(masked_file_path, 'w') as masked_file:
                    masked_file.writelines(masked_content)

def main():
    parser = argparse.ArgumentParser(description='Mask code blocks in TLA+ specification files.')
    parser.add_argument('-i', '--input_dir', required=True, help='Input directory with TLA files.')
    parser.add_argument('-m', '--masked_dir', required=True, help='Output directory for masked TLA files.')
    parser.add_argument('-b', '--blocks', type=int, default=1, help='Number of code blocks to mask per file.')

    args = parser.parse_args()

    mask_code_blocks(args.input_dir, args.masked_dir, args.blocks)

if __name__ == "__main__":
    main()
