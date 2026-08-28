import sys
import time
import subprocess


def fmt_in_pairs(tuples, prepend, bracket):
    brackets = {
        "Parentheses": ("(", ")"),
        "Angle": ("<", ">"),
        "Square": ("[", "]"),
    }
    left, right = brackets[bracket]
    if not tuples:
        return ""
    *rest, last = tuples
    acc = str(last)
    for t in reversed(rest):
        acc = f"{prepend}{left}{t}, {acc}{right}"
    return acc


def gen_nested_eithers(num_of_variants, var_name):
    if num_of_variants == 2:
        return [f"Either::Left({var_name})", f"Either::Right({var_name})"]
    else:
        return [f"Either::Left({var_name})"] + [
            f"Either::Right({nested})"
            for nested in gen_nested_eithers(num_of_variants - 1, var_name)
        ]


def gen_code(num):
    if num < 2:
        raise ValueError("Number of variants must be at least 2")
    code = ""
    # generate the enum
    code += "pub enum Enum {\n"
    variants = []
    for i in range(num):
        variant_type = f"Variant{i}"
        code += f"    {variant_type}(u32),\n"
        variants.append(variant_type)
    code += "}\n"

    # generate the enum inner
    msg_type_inner_name = "EnumInner"
    code += f"pub type {msg_type_inner_name} = {fmt_in_pairs(['u32'] * num, 'Either', 'Angle')};\n"

    nested_eithers = gen_nested_eithers(num, "m")
    code += "    fn convert(m: Enum) -> EnumInner {\n        match m {\n"
    for variant, nested in zip(variants, nested_eithers):
        code += f"            Enum::{variant}(m) => {nested},\n"
    code += "        }\n    }\n"

    code += "    fn convert_inv(m: EnumInner) -> Enum {\n        match m {\n"
    for variant, nested in zip(variants, nested_eithers):
        code += f"            {nested} => Enum::{variant}(m),\n"
    code += "        }\n    }\n"

    return code


def main():
    args = sys.argv
    if len(args) < 3:
        print("Usage: test_fmt_nested.py <verusfmt|rustfmt> <number_of_variants>")
        sys.exit(1)
    fmter = args[1]
    try:
        num_of_variants = int(args[2])
    except ValueError:
        print("Invalid argument, expected a number")
        sys.exit(1)

    code = gen_code(num_of_variants)
    if fmter == "verusfmt":
        file_content = f"""
use vstd::prelude::*;

verus! {{
    enum Either<T, U> {{
        Left(T),
        Right(U),
    }}

    {code}
}}
"""
    elif fmter == "rustfmt":
        file_content = code
    else:
        print("Invalid formatter")
        sys.exit(1)

    outfile = "nested.rs"
    with open(outfile, "w") as f:
        f.write(file_content)
    print(f"Output written to {outfile}")

    # call the formatter on the generated file
    print(f"Running {fmter} on the generated file...")
    start_time = time.time()
    try:
        output = subprocess.run([fmter, outfile], capture_output=True, text=True)
    except Exception as e:
        print(f"Failed to run {fmter}: {e}")
        sys.exit(1)
    if output.returncode != 0:
        print(f"{fmter} failed: {output.stderr}")
    else:
        elapsed = time.time() - start_time
        print(f"{fmter} succeeded in {elapsed:.2f} seconds")


if __name__ == "__main__":
    main()
