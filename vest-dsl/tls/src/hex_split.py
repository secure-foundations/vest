# split a hex string into a space-separated hex string
# Example: 1234567890abcdef -> 12 34 56 78 90 ab cd ef


def hex_split(hex_str):
    return " ".join(hex_str[i : i + 2] for i in range(0, len(hex_str), 2))


if __name__ == "__main__":
    import sys

    # Read the input string from command line argument
    input_string = sys.argv[1]

    # if no command line argument is provided
    # Read the input string from stdin
    if len(sys.argv) == 1:
        input_string = input("Enter a hex string: ")

    # Split the hex string
    output_string = hex_split(input_string)

    # Print the output string
    print(output_string)
