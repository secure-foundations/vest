#!/usr/bin/env python3
import re
import sys
import os

def parse_time(val_str, unit):
    val = float(val_str)
    if unit == 'ns':
        return val
    elif unit in ('µs', 'us'):
        return val * 1000.0
    elif unit == 'ms':
        return val * 1_000_000.0
    elif unit == 's':
        return val * 1_000_000_000.0
    return val

def parse_thrpt(val_str, unit):
    val = float(val_str)
    if unit == 'B/s':
        return val
    elif unit == 'KiB/s':
        return val * 1024.0
    elif unit == 'MiB/s':
        return val * 1024.0 * 1024.0
    elif unit == 'GiB/s':
        return val * 1024.0 * 1024.0 * 1024.0
    return val

def format_comparison(vest_val, hand_val, invert=False):
    if vest_val == 0 or hand_val == 0:
        return "N/A"
    if invert:
        ratio = hand_val / vest_val
    else:
        ratio = vest_val / hand_val

    if ratio >= 0.99 and ratio <= 1.01:
        return "1.00x (equal)"
    elif ratio > 1.0:
        pct = (ratio - 1.0) * 100.0
        return f"{ratio:.2f}x (+{pct:.1f}%)"
    else:
        pct = (1.0 - ratio) * 100.0
        return f"{ratio:.2f}x (-{pct:.1f}%)"

def main():
    script_dir = os.path.dirname(os.path.abspath(__file__))
    default_path = os.path.join(script_dir, "mutual_fix_bench_result.txt")
    
    # Check flags
    as_markdown = "--markdown" in sys.argv
    save_md = "--save" in sys.argv
    
    # Remove flags from arguments to get file path
    args = [a for a in sys.argv[1:] if a not in ("--markdown", "--save")]
    file_path = args[0] if args else default_path
    
    if not os.path.exists(file_path):
        print(f"Error: File not found at {file_path}")
        sys.exit(1)
        
    with open(file_path, "r", encoding="utf-8") as f:
        content = f.read()
        
    benchmarks = {}
    lines = content.split('\n')
    current_bench = None
    current_flavor = None
    
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        if not line:
            i += 1
            continue
            
        progress_match = re.search(r'Benchmarking\s+(\w+)/(\w+):', line)
        if progress_match:
            current_bench, current_flavor = progress_match.group(1), progress_match.group(2)
        else:
            if not any(p in line for p in ('MiB/s', 'KiB/s', 'GiB/s', 'B/s')):
                normal_match = re.search(r'(\w+)/(\w+)', line)
                if normal_match:
                    current_bench, current_flavor = normal_match.group(1), normal_match.group(2)
            
        if current_bench and current_flavor:
            if current_bench not in benchmarks:
                benchmarks[current_bench] = {}
            if current_flavor not in benchmarks[current_bench]:
                benchmarks[current_bench][current_flavor] = {}
                
        if 'time:' in line:
            bracket_match = re.search(r'\[(.*?)\]', line)
            if bracket_match and current_bench and current_flavor:
                inner = bracket_match.group(1).strip()
                tokens = inner.split()
                if len(tokens) == 6:
                    benchmarks[current_bench][current_flavor]['time_raw'] = tokens[2] + " " + tokens[3]
                    benchmarks[current_bench][current_flavor]['time_ns'] = parse_time(tokens[2], tokens[3])
                    
        elif 'thrpt:' in line:
            bracket_match = re.search(r'\[(.*?)\]', line)
            if bracket_match and current_bench and current_flavor:
                inner = bracket_match.group(1).strip()
                tokens = inner.split()
                if len(tokens) == 6:
                    benchmarks[current_bench][current_flavor]['thrpt_raw'] = tokens[2] + " " + tokens[3]
                    benchmarks[current_bench][current_flavor]['thrpt_bps'] = parse_thrpt(tokens[2], tokens[3])
                    
        i += 1

    # 1. Discover all unique flavors across all parsed benchmarks
    all_flavors = set()
    for flavors_dict in benchmarks.values():
        for flavor in flavors_dict.keys():
            all_flavors.add(flavor)
            
    # 2. Determine baseline flavor: containing 'handrolled' (case-insensitive) or first alphabetically
    baseline_flavor = None
    for f in sorted(list(all_flavors)):
        if "handrolled" in f.lower():
            baseline_flavor = f
            break
    if not baseline_flavor and all_flavors:
        baseline_flavor = sorted(list(all_flavors))[0]
        
    # 3. Order flavors: baseline first, then alphabetically
    ordered_flavors = [baseline_flavor] if baseline_flavor else []
    for f in sorted(list(all_flavors)):
        if f != baseline_flavor:
            ordered_flavors.append(f)
            
    # 4. Check if any benchmark has throughput data
    has_throughput = False
    for flavors_dict in benchmarks.values():
        for flavor_data in flavors_dict.values():
            if 'thrpt_raw' in flavor_data:
                has_throughput = True
                break
                
    # 5. Define headers
    headers = ["Benchmark", "Type"]
    for f in ordered_flavors:
        headers.append(f"{f} Time")
    if has_throughput:
        for f in ordered_flavors:
            headers.append(f"{f} Thrpt")
            
    # 6. Build rows
    rows = []
    for bench_name, flavors_dict in sorted(benchmarks.items()):
        if bench_name.endswith("_parse"):
            display_name = bench_name[:-6]
            op_type = "Parse"
        elif bench_name.endswith("_serialize"):
            display_name = bench_name[:-10]
            op_type = "Serialize"
        elif bench_name.endswith("_prepare"):
            display_name = bench_name[:-8]
            op_type = "Prepare"
        else:
            display_name = bench_name
            op_type = "Unknown"
            
        # Get baseline values for comparison
        base_time_ns = 0
        base_thrpt_bps = 0
        if baseline_flavor in flavors_dict:
            base_time_ns = flavors_dict[baseline_flavor].get('time_ns', 0)
            base_thrpt_bps = flavors_dict[baseline_flavor].get('thrpt_bps', 0)
            
        time_cells = []
        for f in ordered_flavors:
            if f in flavors_dict:
                time_raw = flavors_dict[f].get('time_raw', 'N/A')
                time_ns = flavors_dict[f].get('time_ns', 0)
                if f != baseline_flavor and base_time_ns > 0 and time_ns > 0:
                    ratio = base_time_ns / time_ns
                    time_cells.append(f"{time_raw} ({ratio:.2f}x)")
                else:
                    time_cells.append(time_raw)
            else:
                time_cells.append('N/A')
                
        thrpt_cells = []
        if has_throughput:
            for f in ordered_flavors:
                if f in flavors_dict:
                    thrpt_raw = flavors_dict[f].get('thrpt_raw', 'N/A')
                    thrpt_bps = flavors_dict[f].get('thrpt_bps', 0)
                    if f != baseline_flavor and base_thrpt_bps > 0 and thrpt_bps > 0:
                        ratio = thrpt_bps / base_thrpt_bps
                        thrpt_cells.append(f"{thrpt_raw} ({ratio:.2f}x)")
                    else:
                        thrpt_cells.append(thrpt_raw)
                else:
                    thrpt_cells.append('N/A')
                    
        row = [display_name, op_type] + time_cells
        if has_throughput:
            row += thrpt_cells
        rows.append(row)

    if as_markdown:
        # Generate Markdown Table
        md_lines = []
        md_lines.append("| " + " | ".join(headers) + " |")
        md_lines.append("| " + " | ".join(["---"] * len(headers)) + " |")
        for row in rows:
            md_lines.append("| " + " | ".join(row) + " |")
        print("\n".join(md_lines))
    else:
        # Determine column widths
        widths = [len(h) for h in headers]
        for row in rows:
            for i, val in enumerate(row):
                widths[i] = max(widths[i], len(str(val)))
                
        # Print pretty ASCII table
        sep = "+" + "+".join(["-" * (w + 2) for w in widths]) + "+"
        header_str = "|" + "|".join([f" {h.ljust(widths[i])} " for i, h in enumerate(headers)]) + "|"
        double_sep = "+" + "+".join(["=" * (w + 2) for w in widths]) + "+"
        
        print("\nBENCHMARK RESULTS COMPARISON\n")
        print(sep)
        print(header_str)
        print(double_sep)
        
        for row in rows:
            row_str = "|" + "|".join([f" {str(val).ljust(widths[i])} " for i, val in enumerate(row)]) + "|"
            print(row_str)
            print(sep)
            
        if baseline_flavor:
            print(f"\nNote: Values in parentheses show the speedup factor relative to '{baseline_flavor}'.")
            print("      For Time: baseline time / flavor time (higher is better, >1.0x means faster than baseline).")
            print("      For Thrpt: flavor thrpt / baseline thrpt (higher is better, >1.0x means faster than baseline).\n")

    # If --save flag was passed, also save to a markdown file
    if save_md or not as_markdown:
        md_path = os.path.splitext(file_path)[0] + ".md"
        md_lines = []
        md_lines.append("# Benchmark Results Comparison")
        md_lines.append("")
        md_lines.append("| " + " | ".join(headers) + " |")
        md_lines.append("| " + " | ".join(["---"] * len(headers)) + " |")
        for row in rows:
            md_lines.append("| " + " | ".join(row) + " |")
        md_lines.append("")
        if baseline_flavor:
            md_lines.append(f"Note: Values in parentheses show the speedup factor relative to '{baseline_flavor}'.")
            md_lines.append("* For Time: baseline time / flavor time (higher is better, >1.0x means faster than baseline).")
            md_lines.append("* For Thrpt: flavor thrpt / baseline thrpt (higher is better, >1.0x means faster than baseline).")
        
        with open(md_path, "w", encoding="utf-8") as f_out:
            f_out.write("\n".join(md_lines))
        if not as_markdown:
            print(f"Saved markdown summary to: {md_path}\n")

if __name__ == "__main__":
    main()
