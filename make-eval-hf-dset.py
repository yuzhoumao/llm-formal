from datasets import load_dataset, load_metric, Dataset, DatasetDict
import os
import glob

def load_data(nl_descrip_dir, labels_dir):
    data_files = {
        "protocol": [],
        "prompt": [],
        "label": []
    }
    
    # Load the prompt and label data
    for txt_file in glob.glob(os.path.join(nl_descrip_dir, '*.txt')):
        file_name = os.path.splitext(os.path.basename(txt_file))[0]
        data_files['protocol'].append(file_name)

        # Read the natural language description
        with open(txt_file, 'r', encoding='utf-8') as file:
            prompt = file.read()
            prompt = "### Human: Generate a TLA+ module given instructions: " + prompt
            prompt += ". Do not include explanation; only code. ### Assistant: "
            data_files["prompt"].append(prompt)
        
        # Read the corresponding label file
        label_file_path = os.path.join(labels_dir, f"{file_name}_label.txt")
        with open(label_file_path, 'r', encoding='utf-8') as file:
            label = file.read()
            data_files["label"].append(label)

    return data_files

def create_hf_dataset(data_files):
    # Create a Dataset object
    dataset = Dataset.from_dict(data_files, split='val')
    return dataset

def push_to_hf_hub(dataset, dataset_name):
    dataset.push_to_hub(dataset_name, token="")
    print(f"Dataset pushed to the Hub under: https://huggingface.co/datasets/{dataset_name}")

# Define your directories
nl_descrip_dir = ''
labels_dir = ''

# Load data
data_files = load_data(nl_descrip_dir, labels_dir)

# Create the dataset
dataset = create_hf_dataset(data_files)

# Define the name of the dataset to be pushed
dataset_name = 'tla_code_eval'

# Push the dataset to Hugging Face Hub
push_to_hf_hub(dataset, dataset_name)
