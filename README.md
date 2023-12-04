# llm-formal
Using LLMs to generate formal verification programs or mathematical proofs for distributed protocols

## Dataset
`TLA+_code` directory contains the custom training dataset. Each file contains a human instruction relating to generating specific TLA+ code, as well as a response from the assistant (language model) that contains a correctly written TLA+ specification.
`input` directory contains a series of subdirectories, each of which contains all the code and files necessary for the protocol to pass the TLC checker. This includes the TLA specification files as well as various configuration files.
`masked_input` directory contains TLA files from the `input` directory with one code block masked. the goal is to have the LLM generate that code block that's missing.

## Models
We used the LLaMA-2 model by Meta AI in our initial experiments, but pivoted to use codellama (`codellama/CodeLlama-7b-hf`) and subsequently fine-tuned that model on our custom training set. The fine-tuning script is provided by trl (https://github.com/huggingface/trl/blob/main/examples/scripts/sft.py). We load the 4-bit version of the codellama model because of GPU constraints. We do not include the training script in this repository, but can be used by creating a bash script such as:
```
python trl/examples/scripts/sft.py \
    --model_name codellama/CodeLlama-7b-Instruct-hf \
    --dataset_name aneeshas/tla_code_train \
    --use_peft \
    --load_in_4bit \
    --num_train_epochs 10 \
    --use_auth_token yes \
    --batch_size 4 \
    --output_dir codellama-finetune \
    --gradient_accumulation_steps 2
```
