import argparse
import pandas as pd
import os
import sys
import time
from pathlib import Path


def create_dir_if_needed(dir_name):
    Path(dir_name).mkdir(parents=True, exist_ok=True)


def get_subdirs(d):
    return set(sub for sub in os.listdir(d) if os.path.isdir(os.path.join(d, sub)))


def discover_tags(prefix):
    """
    Identifies all TARGET directories and verifies they all
    contain the exact same set of subdirectories (Tags).
    """
    all_entries = os.listdir('.')
    target_dirs = sorted([d for d in all_entries if os.path.isdir(d) and d.startswith(prefix)])

    if not target_dirs:
        print(f"Error: No folders found starting with prefix: '{prefix}'")
        sys.exit(1)

    # Use first directory as the gold standard
    master_target = target_dirs[0]
    master_tags = get_subdirs(master_target)

    if not master_tags:
        print(f"Error: No subdirectories (tags) found in '{master_target}'.")
        sys.exit(1)

    # Verify consistency
    mismatched = False
    for td in target_dirs[1:]:
        current_tags = get_subdirs(td)
        if current_tags != master_tags:
            mismatched = True
            missing = master_tags - current_tags
            extra = current_tags - master_tags
            print(f"Structure Mismatch in '{td}':")
            if missing: print(f"  - Missing: {missing}")
            if extra:   print(f"  - Extra: {extra}")

    if mismatched:
        sys.exit(1)

    print(f"Verification successful. Targets: {len(target_dirs)}, Tags: {len(master_tags)}")
    return sorted(master_tags)


def find_files_by_prefix_and_tag(prefix, tag):
    """
    1. Finds all directories in current path starting with 'prefix'.
    2. Finds all .csv files inside those directories that contain 'tag'.
    """
    matched_files = []

    all_entries = os.listdir('.')
    target_dirs = [d for d in all_entries if os.path.isdir(d) and d.startswith(prefix)]

    if not target_dirs:
        print(f"Error: No directories found starting with prefix: '{prefix}'")
        sys.exit(1)

    for d in target_dirs:
        # Find csv files inside the directory that match the tag
        for f in os.listdir(d):
            if f.startswith(tag) and f.endswith('.csv'):
                matched_files.append(os.path.join(d, f))

    if not matched_files:
        print(f"Error: Found directories, but no CSV files inside matched the tag: '{tag}'")
        sys.exit(1)

    print(f"Found {len(matched_files)} files across {len(target_dirs)} directories.")
    return sorted(matched_files) # Sorted ensures consistent column ordering


def combine(tag, files, avg_cols, add_cols, mul_cols, meta_path, out_name):
    all_dataframes = [pd.read_csv(f) for f in files]
    df = pd.concat(all_dataframes, axis=1)

    if meta_path and os.path.isfile(Path(meta_path) / f'{tag}.csv'):
        print(f'File extra csv file: {Path(meta_path)}/{tag}.csv')
        extra_df = pd.read_csv(Path(meta_path) / f'{tag}.csv')
        df = pd.concat([extra_df, df], axis=1)

    for avg_col in avg_cols:
        cols_to_average = [col for col in df.columns if col.endswith(avg_col)]
        df[f'{tag}-avg:{avg_col}'] = df[cols_to_average].mean(axis=1, skipna=True)

    for add_col in add_cols:
        dest = add_col[0]
        src = add_col[1:]
        df[dest] = df[src].sum(axis=1, min_count=len(add_col[1:]))

    # special operation: mul_col is length 3
    for mul_col in mul_cols:
        dest = mul_col[0]
        src = mul_col[1:]
        df[dest] = (2 ** df[src[1]]) * df[src[0]]

    print(f'Write to {out_name}')
    df.to_csv(out_name, index=False)


def process(opts):
    tags = discover_tags(opts.prefix)

    for tag in tags:
        print(f'Process: {tag}')

        files = find_files_by_prefix_and_tag(opts.prefix, tag)
        avg_cols = ['qiskit-simulation', 'qsim-simulation', 'qtorch-simulation', 'iso-to-perpl', 'perpl-to-fgg', 'iso-to-fgg']
        add_cols = [[f'{tag}-avg:iso-perpl-fgg', f'{tag}-avg:perpl-to-fgg', f'{tag}-avg:iso-to-fgg'],
                    [f'{tag}-no_opt:iso-perpl-fgg-total', f'{tag}-no_opt:iso-simulation',
                     f'{tag}-no_opt:iso-to-perpl', f'{tag}-no_opt:perpl-to-fgg'],
                    [f'{tag}-exp_opt:iso-perpl-fgg-total', f'{tag}-exp_opt:iso-simulation',
                     f'{tag}-exp_opt:iso-to-perpl', f'{tag}-exp_opt:perpl-to-fgg'],
                    [f'{tag}-all_opt:iso-perpl-fgg-total', f'{tag}-all_opt:iso-simulation',
                     f'{tag}-all_opt:iso-to-perpl', f'{tag}-all_opt:perpl-to-fgg'],
                    [f'{tag}-no_opt:iso-fgg-total', f'{tag}-no_opt:iso-fgg-simulation', f'{tag}-no_opt:iso-to-fgg'],
                    [f'{tag}-exp_opt:iso-fgg-total', f'{tag}-exp_opt:iso-fgg-simulation', f'{tag}-exp_opt:iso-to-fgg'],
                    [f'{tag}-all_opt:iso-fgg-total', f'{tag}-all_opt:iso-fgg-simulation', f'{tag}-all_opt:iso-to-fgg']
                    ]
        mul_cols = [[f'{tag}-avg:qtorch-simulation-full', f'{tag}-avg:qtorch-simulation', f'qubit-number']]
        output_path = Path(opts.output_path) / f'{tag}.csv'

        combine(tag, files, avg_cols, add_cols, mul_cols, opts.extra_path, output_path)

def main():
    parser = argparse.ArgumentParser(description="Combine benchmark data")
    parser.add_argument(
        'prefix',
        type=str,
        help='Prefix of the directory names to search (e.g., "benchmark_")'
    )
    parser.add_argument(
        '-o', '--output_path',
        metavar='<csv_path>',
        type=str,
        default=".",
        help="""Output folder for the combined benchmark report csv files.
        The folder will be created if not exist."""
    )
    parser.add_argument(
        '-e', '--extra_path',
        metavar='<extra_path>',
        type=str,
        default=None,
        help="""Path to the extra metadata csv that are combined with each data
        table."""
    )

    args = parser.parse_args()
    create_dir_if_needed(args.output_path)
    process(args)

if __name__ == "__main__":
    main()
