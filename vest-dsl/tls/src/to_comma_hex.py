import sys

# Get the input string from the command line argument
input_string = sys.argv[1]

if sys.argv[1] == 1:
    # Read the input string from stdin
    input_string = input("Enter a string of hexadecimal numbers separated by spaces: ")

# Split the input into tokens based on whitespace
tokens = input_string.strip().split()
# Convert each token to an integer and format it as '0xXX'
formatted_tokens = ["0x%02x" % int(token, 16) for token in tokens]
# Join the formatted tokens with commas
output_string = ", ".join(formatted_tokens)
# Print the result
print(output_string)
