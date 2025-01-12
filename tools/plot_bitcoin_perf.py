import os
import json
import base64
import argparse

import matplotlib.pyplot as plt
import seaborn as sns


RUST_BTC_BENCH_PREFIX = "rust_bitcoin_"
VEST_BTC_BENCH_PREFIX = "vest_"


def get_sample(i, target_criterion, group, prefix):
    estimate_path = os.path.join(
        target_criterion,
        group,
        prefix + str(i),
        "new/estimates.json",
    )

    with open(estimate_path) as f:
        estimates = json.load(f)

    return estimates["mean"]["point_estimate"]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input_file", type=str, help="Input block samples")
    parser.add_argument("group", type=str, help="Criterion group name")
    parser.add_argument("target_criterion", type=str, help="Path to target/criterion")
    args = parser.parse_args()

    with open(args.input_file) as f:
        block_samples = [(i, len(base64.b64decode(line)) / 1000) for i, line in enumerate(f.readlines())]
        block_samples.sort(key=lambda t: t[1])

        rust_btc = []
        vest_btc = []

        for i, _ in block_samples:
            rust_btc.append(get_sample(i, args.target_criterion, args.group, RUST_BTC_BENCH_PREFIX) / 1000)
            vest_btc.append(get_sample(i, args.target_criterion, args.group, VEST_BTC_BENCH_PREFIX) / 1000)

    print("vest mean:", sum(vest_btc) / len(vest_btc))
    print("rust btc mean:", sum(rust_btc) / len(rust_btc))

    fig, (axis1, axis2) = plt.subplots(1, 2, sharey="row", width_ratios=[2, 5])
    fig.set_size_inches(10, 4)

    # Plot boxplots (x axis = [vest_btc, rust_btc])
    sns.boxplot(data=[vest_btc, rust_btc], ax=axis1)
    axis1.set_xticks([0, 1])
    axis1.set_xticklabels(["Vest", "Rust Bitcoin"])
    axis1.set_ylabel("Time (µs)")

    # Plot scatter graph with small dots
    axis2.scatter(tuple(t[1] for t in block_samples), vest_btc, label="Vest", s=1)
    axis2.scatter(tuple(t[1] for t in block_samples), rust_btc, label="Rust Bitcoin", s=1)
    axis2.set_xlabel("Block size (KB)")
    axis2.legend()

    fig.suptitle("Performance on serializing 1K Bitcoin blocks")

    plt.tight_layout()
    # plt.show()
    plt.savefig("bitcoin_perf.pdf")


if __name__ == "__main__":
    main()
