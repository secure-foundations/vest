import os
import re
import matplotlib.pyplot as plt
import numpy as np

def parse_results(filepath):
    # Regex to capture the benchmark name (e.g. bitcoin_parse/generated_parser)
    bench_re = re.compile(r"^([a-zA-Z0-9_]+)/([a-zA-Z0-9_]+)\s*$")
    # Matches time: [161.25 ms 161.41 ms 161.59 ms] or [82.206 µs 82.400 µs 82.606 µs]
    time_re = re.compile(r"^\s*time:\s*\[\s*[0-9\.]+\s+[a-zA-Zµ]+\s+([0-9\.]+)\s+([a-zA-Zµ]+)\s+[0-9\.]+\s+[a-zA-Zµ]+\s*\]")
    # Matches thrpt: [4.0637 GiB/s 4.0680 GiB/s 4.0721 GiB/s] or [864.89 MiB/s 867.05 MiB/s 869.10 MiB/s]
    thrpt_re = re.compile(r"^\s*thrpt:\s*\[\s*[0-9\.]+\s+[a-zA-Z/]+\s+([0-9\.]+)\s+([a-zA-Z/]+)\s+[0-9\.]+\s+[a-zA-Z/]+\s*\]")
    
    data = []
    current_bench = None
    
    if not os.path.exists(filepath):
        print(f"Error: File {filepath} not found.")
        return data
        
    with open(filepath, 'r') as f:
        for line in f:
            line_str = line.strip()
            bench_match = bench_re.match(line_str)
            if bench_match:
                current_bench = {
                    "category": bench_match.group(1),
                    "impl": bench_match.group(2)
                }
                data.append(current_bench)
                continue
                
            if current_bench is not None:
                time_match = time_re.match(line)
                if time_match:
                    val = float(time_match.group(1))
                    unit = time_match.group(2)
                    current_bench["time_val"] = val
                    current_bench["time_unit"] = unit
                    
                thrpt_match = thrpt_re.match(line)
                if thrpt_match:
                    val = float(thrpt_match.group(1))
                    unit = thrpt_match.group(2)
                    current_bench["thrpt_val"] = val
                    current_bench["thrpt_unit"] = unit
                    # Convert to normalized throughput (GB/s)
                    if "GiB" in unit:
                        current_bench["thrpt_gb"] = val
                    elif "MiB" in unit:
                        current_bench["thrpt_gb"] = val / 1024.0
                    else:
                        current_bench["thrpt_gb"] = val
    return data

def main():
    script_dir = os.path.dirname(os.path.abspath(__file__))
    results_path = os.path.join(script_dir, "results.txt")
    print(f"Reading results from {results_path}...")
    benchmarks = parse_results(results_path)
    
    if not benchmarks:
        print("No benchmarks parsed. Exiting.")
        return
        
    print(f"Parsed {len(benchmarks)} benchmarks successfully.")
    for b in benchmarks:
        print(f" - {b['category']}/{b['impl']}: {b.get('time_val')} {b.get('time_unit')} | {b.get('thrpt_val')} {b.get('thrpt_unit')}")
        
    # Group by category: bitcoin_parse, bitcoin_serialize, tls_parse, tls_serialize
    categories = ["bitcoin_parse", "bitcoin_serialize", "tls_parse", "tls_serialize"]
    
    # Modern styling
    plt.style.use('seaborn-v0_8-whitegrid' if 'seaborn-v0_8-whitegrid' in plt.style.available else 'default')
    fig, axes = plt.subplots(2, 2, figsize=(14, 10), sharex=False)
    fig.suptitle("Benchmark Results: Vest-Generated vs Hand-Written Libraries", fontsize=18, fontweight='bold', color='#1a1a1a')
    
    # Color palette
    colors = {
        "vest": "#3a86c8",  # Sleek Blue
        "library": "#c85a5a"  # Sleek Red
    }
    
    axes_flat = axes.flatten()
    
    for idx, cat in enumerate(categories):
        ax = axes_flat[idx]
        cat_benches = [b for b in benchmarks if b["category"] == cat]
        
        if not cat_benches:
            ax.text(0.5, 0.5, f"No data for {cat}", ha='center', va='center')
            continue
            
        # Separate generated vs library
        vest_bench = next((b for b in cat_benches if "generated" in b["impl"]), None)
        lib_bench = next((b for b in cat_benches if "library" in b["impl"]), None)
        
        labels = []
        throughputs = []
        bar_colors = []
        
        bar_types = []
        if vest_bench:
            labels.append(f"Vest (Generated)\n({vest_bench['time_val']} {vest_bench['time_unit']})")
            throughputs.append(vest_bench["thrpt_gb"])
            bar_colors.append(colors["vest"])
            bar_types.append("vest")
        if lib_bench:
            lib_name = "rust-bitcoin" if "bitcoin" in cat else "rustls"
            labels.append(f"{lib_name} (Hand-Written)\n({lib_bench['time_val']} {lib_bench['time_unit']})")
            throughputs.append(lib_bench["thrpt_gb"])
            bar_colors.append(colors["library"])
            bar_types.append("lib")
            
        x = np.arange(len(labels))
        bars = ax.bar(x, throughputs, color=bar_colors, width=0.5, edgecolor='black', linewidth=0.7)
        
        ax.set_xticks(x)
        ax.set_xticklabels(labels, fontsize=12, fontweight='semibold')
        ax.set_ylabel("Throughput (GB/s)", fontsize=12, fontweight='semibold')
        
        # Title of subplot
        title_map = {
            "bitcoin_parse": "Bitcoin Block Parsing (Throughput)",
            "bitcoin_serialize": "Bitcoin Block Serialization (Throughput)",
            "tls_parse": "TLS Handshake Parsing (Throughput)",
            "tls_serialize": "TLS Handshake Serialization (Throughput)"
        }
        ax.set_title(title_map.get(cat, cat.replace('_', ' ').title()), fontsize=14, fontweight='bold', pad=15)
        
        # Calculate speedup
        speedup = 1.0
        if vest_bench and lib_bench:
            speedup = vest_bench["thrpt_gb"] / lib_bench["thrpt_gb"]
            
        # Add value labels on top of the bars
        for idx, bar in enumerate(bars):
            height = bar.get_height()
            btype = bar_types[idx]
            if btype == "vest":
                ann_text = f"{height:.3f} GB/s ({speedup:.2f}x)"
            else:
                ann_text = f"{height:.3f} GB/s (1.00x)"
            ax.annotate(ann_text,
                        xy=(bar.get_x() + bar.get_width() / 2, height),
                        xytext=(0, 5),  # 5 points vertical offset
                        textcoords="offset points",
                        ha='center', va='bottom', fontsize=10, fontweight='bold')
        
        # Improve grid lines
        ax.grid(axis='y', linestyle='--', alpha=0.7)
        # Extra space on top for labels
        ax.set_ylim(0, max(throughputs) * 1.3 if throughputs else 1.0)
        
    plt.tight_layout(rect=[0, 0, 1, 0.95])
    output_png = os.path.join(script_dir, "benchmark_results.png")
    plt.savefig(output_png, dpi=300)
    print(f"Successfully generated and saved plot to {output_png}")

if __name__ == "__main__":
    main()
