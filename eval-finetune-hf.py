import transformers
from transformers import AutoTokenizer, pipeline
from datasets import load_dataset

# Set the model path
model = ""

tokenizer = AutoTokenizer.from_pretrained(model)
text_generator = pipeline(
    "text-generation",
    model=model,
    device_map="auto",
)

# Load the dataset from Hugging Face Hub
dataset = load_dataset('aneeshas/tla_masked_code_eval', split='train')

baseline_prompt = "### Human: generate the TLA+ code that is missing from the section labeled `(* MASKED CODE *)`. "
baseline_prompt += "Do not include explanation; only TLA+ code. Provide only the code that should replace "
baseline_prompt += "`(* MASKED CODE *)`, and no other code.\n"

specific_prompt = "### Human: You are a helpful, respectful and honest assistant skilled in a formal verification language called TLA+. "
specific_prompt += "Remember you are a code assistant. Fill in TLA+ code that is missing from the following TLA+ specification of a protocol."
specific_prompt += "Do not include explanation; only TLA+ code. Provide only the code that should replace "
specific_prompt += "`(* MASKED CODE *)`, and no other code.\n"

contextual_prompt = "### Human: You are a helpful, respectful and honest assistant skilled in a formal verification language called TLA+. "
contextual_prompt += "Remember you are an assistant. The following specfication is correct except that it's missing a block of code. "
contextual_prompt += "Fill in TLA+ code that is missing from the following specification."
contextual_prompt += "Do not include explanation; only TLA+ code. Provide only the code that should replace "
contextual_prompt += "`(* MASKED CODE *)`, and no other code.\n"

example_prompt = "### Human: You are a helpful, respectful and honest assistant skilled in a formal verification language called TLA+. "
example_prompt += "The following specfication is correct except that it's missing a block of code. Fill in TLA+ code that is missing from the following specification. For example, given the following specification: "
example_prompt += "\n```--------------------------- MODULE SlidingPuzzles --------------------------- EXTENDS Integers VARIABLE board W == 4 H == 5 Pos == (0 .. W - 1) \X (0 .. H - 1) Piece == SUBSET Pos Klotski == {{<<0, 0>>, <<0, 1>>}, {<<1, 0>>, <<2, 0>>, <<1, 1>>, <<2, 1>>}, {<<3, 0>>, <<3, 1>>},{<<0, 2>>, <<0, 3>>}, {<<1, 2>>, <<2, 2>>},{<<3, 2>>, <<3, 3>>}, {<<1, 3>>}, {<<2, 3>>}, {<<0, 4>>}, {<<3, 4>>}} KlotskiGoal == {<<1, 3>>, <<1, 4>>, <<2, 3>>, <<2, 4>>} \notin board ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x TypeOK == board \in SUBSET Piece (***************************************************************************) (* Given a position and a set of empty positions return a set of *) (* appropriately filtered von Neumann neighborhood points *) (***************************************************************************) dir(p, es) == LET dir == {<<1, 0>>, <<0, 1>>, <<-1, 0>>, <<0, -1>>} IN {d \in dir : /\ <<p[1] + d[1], p[2] + d[2]>> \in Pos /\ <<p[1] + d[1], p[2] + d[2]>> \notin es} (***************************************************************************) (* Given a position and a unit translation vector return a pair of *) (* pieces, before and after translation in opposite this vector direction *) (***************************************************************************) move(p, d) == LET s == <<p[1] + d[1], p[2] + d[2]>> pc == ChooseOne(board, LAMBDA pc : s \in pc) IN <<pc, {<<q[1] - d[1], q[2] - d[2]>> : q \in pc}>> (***************************************************************************) (* Given specific free position and a set of all free positions return *) (* a set of boards updated by moving appropriate pieces to that *) (* free position *) (***************************************************************************) update(e, es) == LET dirs == dir(e, es) moved == {move(e, d) : d \in dirs} free == {<<pc, m>> \in moved : /\ m \cap (UNION (board \ {pc})) = {} /\ \A p \in m : p \in Pos} IN {(board \ {pc}) \cup {m} : <<pc, m>> \in free} Init == board = Klotski (* MASKED CODE *) =============================================================================```\n"
example_prompt += "The correct output would be:\n ```Next == LET empty == Pos \ UNION board IN \E e \in empty : board' \in update(e, empty)```\n"
example_prompt += "Do not include explanation; only TLA+ code. Provide only the code that should replace "
example_prompt += "`(* MASKED CODE *)`, and no other code.\n"

# Iterate through the dataset
for example in dataset:
    protocol_name = example['protocol']
    print(f'Writing code for {protocol_name}.')
    prompt = example['prompt']
    prompt = prompt.replace(baseline_prompt, example_prompt)
    sequences = text_generator(
        prompt,
        do_sample=True,
        top_k=1,
        num_return_sequences=1,
        eos_token_id=tokenizer.eos_token_id,
        max_length=4096,
    )

    out_str = sequences[0]['generated_text'].split("\n", 1)[1] + '\n'

    # The filename can be derived from the example ID or another unique identifier
    output_filename = f'/{protocol_name}_llama_code.txt'
    with open(output_filename, 'w') as output_file:
        output_file.write(out_str)
    print(f'Wrote {protocol_name} to file.')

print("Processing complete!")
