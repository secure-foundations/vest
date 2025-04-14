import sys
import time
import base64
import random
import requests
import argparse


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("max_height", type=int, help="The maximum height of blocks to sample from")
    parser.add_argument("num_blocks", type=int, help="The numble of samples")
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    random.seed(args.seed)
    block_heights = random.sample(range(args.max_height + 1), args.num_blocks)

    # print("pub const TEST_BLOCKS: &[&[u8]] = &[")

    for height in block_heights:
        url = f"https://api.blockchair.com/bitcoin/raw/block/{height}"

        while True:
            response = requests.get(url)
            if response.status_code == 200:
                break

            # Might have hit the lmit, retrying
            print(f"non-200 status code: {response.status_code}: {response.text}", file=sys.stderr)
            time.sleep(1)

        data = response.json()["data"]
        if type(data) is list:
            hex_data = response.json()["data"][0]["raw_block"]
        else:
            hex_data = response.json()["data"][str(height)]["raw_block"]

        print(f"fetched height {height} ({len(hex_data) // 2} bytes)", file=sys.stderr)

        assert len(hex_data) % 2 == 0

        print(base64.b64encode(bytes.fromhex(hex_data)).decode())

        # print('    b"' + "".join(f"\\x{hex_data[i]}{hex_data[i + 1]}" for i in range(0, len(hex_data), 2)) + '",')
    # print("];")


if __name__ == "__main__":
    main()
