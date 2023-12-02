from datasets import load_dataset, load_metric, Dataset, DatasetDict
import os

# Step 1: Load text files from a directory into a HuggingFace dataset
def load_text_files_from_directory(directory_path):
    files = [os.path.join(directory_path, f) for f in os.listdir(directory_path) if f.endswith('.txt')]
    texts = []
    for file in files:
        with open(file, 'r') as f:
            texts.append(f.read())
    return Dataset.from_dict({'text': texts}, split='train')

# Set your folder path
folder_path = ''

# Load dataset
dataset = load_text_files_from_directory(folder_path)
dataset_dict = DatasetDict({
    'train': dataset
})

# Step 2: Push the dataset to the Hugging Face Hub

# You should be logged in to push to the Hub. You can use "huggingface-cli login" for that.
dataset_name = 'tla_code_train'
dataset_dict.push_to_hub(dataset_name, token="")

print(f"Dataset pushed to the Hub under: https://huggingface.co/datasets/{dataset_name}")

