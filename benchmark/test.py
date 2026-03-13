#!/usr/bin/env python3

import os
import sys
import argparse
import subprocess
import time
import shlex
import resource
import csv
import textwrap
import logging
import psutil
from itertools import zip_longest
from natsort import natsorted
from pathlib import Path
from tqdm import tqdm
logger = logging.getLogger(__name__)

def limit_resources(memory_gb):
    max_bytes = int(memory_gb * 1024**3)
    resource.setrlimit(resource.RLIMIT_AS, (max_bytes, max_bytes))

def get_safe_memory_limit(ratio=0.95):
    total = psutil.virtual_memory().total
    return int(total * ratio / 1024 ** 3)

def create_dir_if_needed(dir_name):
    Path(dir_name).mkdir(parents=True, exist_ok=True)


def check_tool(tool_path):
    if not Path(tool_path).is_file():
        print(f"{Path(tool_path).resolve()} doesn't exist! Make sure the tool exists!")
        sys.exit(1)


def check_tools(opts):
    BENCHMARK_ROOT_DIR=opts.benchmark_root
    ISO_EXE_PATH = f"{BENCHMARK_ROOT_DIR}/.."
    PERPL_EXE_PATH = f"{BENCHMARK_ROOT_DIR}/../../perpl"
    FGG_EXE_PATH = f"{BENCHMARK_ROOT_DIR}/../../perpl/fggs"

    check_tool(f"{ISO_EXE_PATH}/iso-exe")
    check_tool(f"{PERPL_EXE_PATH}/perplc")
    check_tool(f"{FGG_EXE_PATH}/bin/sum_product.py")


def run_command(dir_path, isuffix, osuffix, cmd, result_dir, iopt, oopt, tag, opts):
    timeout_seconds = opts.time_limit * 60

    create_dir_if_needed(result_dir)

    files = natsorted(
        Path(dir_path).rglob(f"*{isuffix}"),
        key=lambda p: p.name
    )
    if (opts.case_limit > 0):
        files = files[0:opts.case_limit]

    short_tag = textwrap.shorten(tag, width=15)
    time_data = []
    for ifile in tqdm(files,
                      desc=short_tag,
                      bar_format="{desc:<10} |{bar}| {n_fmt}/{total_fmt} [{elapsed}<{remaining}]"):
        ofile = ifile.stem + osuffix
        output_path = Path(result_dir) / ofile

        full_cmd = []

        full_cmd.extend(cmd.split())
        if iopt: full_cmd.append(iopt)
        full_cmd.append(str(ifile))

        if oopt == ">":
            out_port = open(output_path, "w")
        elif oopt:
            full_cmd.append(oopt)
            full_cmd.append(str(output_path))
            out_port = sys.stdout
        else:
            out_port = sys.stdout
        if oopt == ">":
            pretty_cmd = shlex.join(full_cmd) + f" > {output_path}"
        else:
            pretty_cmd = shlex.join(full_cmd)
        logger.info(f'{pretty_cmd}')

        normal = True
        time_diff = 0
        if opts.dry_run:
            tqdm.write(pretty_cmd)
        else:
            start = time.time()
            try:
                result = subprocess.run(
                    full_cmd,
                    stdout=out_port,
                    stderr=subprocess.PIPE,
                    timeout=timeout_seconds,
                    preexec_fn=lambda: limit_resources(opts.memory_limit))
                normal = (result.returncode == 0)
                if result.stderr:
                    logger.error("Subprocess stderr:\n%s", result.stderr.decode("utf-8"))
            except subprocess.TimeoutExpired:
                tqdm.write(f"[TIMEOUT] {cmd}")
                logger.info(f"[EXCEPTION] {cmd}")
                normal = False
            except Exception as e:
                tqdm.write(f"[EXCEPTION] {e}")
                logger.info(f"[EXCEPTION] {e}")
                normal = False

            end = time.time()
            time_diff = end - start

        if oopt == ">":
            out_port.close()

        if not normal:
            tqdm.write(f"Stop at {ifile}", file=sys.stderr)
            logger.info(f"Stop at {ifile}")
            break
        else:
            time_data.append(time_diff)

    return time_data

def run_benchmark(suite_name, opts):
    BENCHMARK_ROOT_DIR=opts.benchmark_root
    ISO_EXE_PATH = f"{BENCHMARK_ROOT_DIR}/.."
    PERPL_EXE_PATH = f"{BENCHMARK_ROOT_DIR}/../../perpl"
    FGG_EXE_PATH = f"{BENCHMARK_ROOT_DIR}/../../perpl/fggs"

    iso_suite_dir = f"{BENCHMARK_ROOT_DIR}/{suite_name}/iso"
    qiskit_suite_dir = f"{BENCHMARK_ROOT_DIR}/{suite_name}/qiskit"
    qsim_suite_dir = f"{BENCHMARK_ROOT_DIR}/{suite_name}/qsim"
    qtorch_suite_dir = f"{BENCHMARK_ROOT_DIR}/{suite_name}/qtorch"

    ppl_dir = f"{BENCHMARK_ROOT_DIR}/{suite_name}/ppl"
    json_dir = f"{BENCHMARK_ROOT_DIR}/{suite_name}/json"
    iso_result_dir = f"{BENCHMARK_ROOT_DIR}/{suite_name}/iso-text"
    qiskit_result_dir = f"{BENCHMARK_ROOT_DIR}/{suite_name}/qiskit-text"
    iso_fgg_dir = f"{BENCHMARK_ROOT_DIR}/{suite_name}/iso-fgg"
    iso_fgg_result_dir = f"{BENCHMARK_ROOT_DIR}/{suite_name}/iso-fgg-text"
    qsim_result_dir = f"{BENCHMARK_ROOT_DIR}/{suite_name}/qsim-text"
    qtorch_result_dir = f"{BENCHMARK_ROOT_DIR}/{suite_name}/qtorch-text"

    tqdm.write(f'Running the benchmark {suite_name}')
    logger.info(f'Running the benchmark {suite_name}')

    row_tag = f'{suite_name}-{opts.tag}'
    tags = [f'{row_tag}:iso-to-perpl',
            f'{row_tag}:perpl-to-fgg',
            f'{row_tag}:iso-simulation',
            f'{row_tag}:iso-to-fgg',
            f'{row_tag}:iso-fgg-simulation',
            f'{row_tag}:qiskit-simulation',
            f'{row_tag}:qsim-simulation',
            f'{row_tag}:qtorch-simulation']

    iso_to_perpl = run_command(
        iso_suite_dir, ".iso", ".ppl",
        f"{ISO_EXE_PATH}/iso-exe perpl",
        ppl_dir, "", "-o", tags[0], opts
    )

    perpl_to_fgg = run_command(
        ppl_dir, ".ppl", ".json",
        f"{PERPL_EXE_PATH}/perplc",
        json_dir, "-s", ">", tags[1], opts
    )

    iso_simulation = run_command(
        json_dir, ".json", "-iso.txt",
        f"python {FGG_EXE_PATH}/bin/sum_product.py",
        iso_result_dir, "-d", ">", tags[2], opts
    )

    iso_to_fgg = run_command(
        iso_suite_dir, ".iso", "-iso-fgg.json",
        f"{ISO_EXE_PATH}/iso-exe fgg",
        iso_fgg_dir, "-c", "-o", tags[3], opts
    )

    iso_fgg_simulation = run_command(
        iso_fgg_dir, ".json", "-iso.txt",
        f"python {FGG_EXE_PATH}/bin/sum_product.py",
        iso_fgg_result_dir, "-d", ">", tags[4], opts
    )

    qiskit_simulation = run_command(
        qiskit_suite_dir, ".py", "-qiskit.txt",
        "python",
        qiskit_result_dir, "", ">", tags[5], opts
    )

    qsim_simulation = run_command(
        qsim_suite_dir, ".py", "-qsim.txt",
        "python",
        qsim_result_dir, "", ">", tags[6], opts
    )

    qtorch_simulation = run_command(
        qtorch_suite_dir, ".sim", "-qtorch.txt",
        "qtorch",
        qtorch_result_dir, "", ">", tags[7], opts
    )

    if not opts.dry_run:
        output_csv = Path(opts.csv_path) / f'{suite_name}-{opts.tag}-{time.strftime("%Y-%m-%d_%H-%M-%S")}.csv'
        with open(output_csv, "w", newline="") as f:
            writer = csv.writer(f)
            writer.writerow(tags)

            for row in zip_longest(iso_to_perpl, perpl_to_fgg, iso_simulation,
                                   iso_to_fgg, iso_fgg_simulation,
                                   qiskit_simulation, qsim_simulation, qtorch_simulation,
                                   fillvalue=""):
                writer.writerow(row)

def run_test(opts):
    run_benchmark("had-last-qubit", opts)
    run_benchmark("deutsch-jozsa-to-zero-simplified", opts)
    run_benchmark("deutsch-jozsa-is-even-simplified", opts)
    run_benchmark("deutsch-jozsa-is-even", opts)
    run_benchmark("simon", opts)
    run_benchmark("qft", opts)


def main():
    parser = argparse.ArgumentParser(description="Run benchmark tests")
    parser.add_argument(
        'benchmark_root',
        type=str,
        help="Root directory of the benchmark"
    )
    parser.add_argument(
        'csv_path',
        metavar='<csv_path>',
        type=str,
        help="""Output folder for the benchmark report csv files.
        The folder will be created if not exist."""
    )
    parser.add_argument(
        "--case_limit",
        dest='case_limit',
        type=int,
        default=0,
        help="[For debugging] Limit how many cases to run for each benchmark. Default is 0, meaning no limit."
    )
    parser.add_argument(
        "-d", "--dry_run",
        action="store_true",
        help="dry run the file"
    )
    parser.add_argument(
        "-t", "--time_limit",
        metavar='<time>',
        dest='time_limit',
        type=float,
        default=5,
        help="Time limit for each test in minutes."
    )
    parser.add_argument(
        "-m", "--memory_limit",
        metavar='<memory>',
        dest='memory_limit',
        type=float,
        default=get_safe_memory_limit(),
        help="Memory limit for each test in GB."
    )
    parser.add_argument(
        "--tag",
        metavar='<memory>',
        dest='tag',
        type=str,
        default="",
        help="A tag for the benchmark."
    )
    parser.add_argument(
        "--log",
        dest='log_path',
        type=str,
        default="log",
        help="Path to the log file."
    )

    args = parser.parse_args()
    create_dir_if_needed(args.csv_path)
    logging.basicConfig(level=logging.INFO,
                        format='%(asctime)s.%(msecs)03d %(levelname)-8s %(message)s',
                        datefmt="%Y-%m-%d_%H:%M:%S",
                        filename=f'{args.log_path}-{time.strftime("%Y-%m-%d_%H-%M-%S")}.log',
                        filemode='w')
    check_tools(args)
    run_test(args)


if __name__ == "__main__":
    main()
