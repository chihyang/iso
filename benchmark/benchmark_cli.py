#!/usr/bin/env python3
"""Unified benchmark CLI.

Modes:
- run: full pipeline
- generate: generate benchmark data
- bench: benchmark execution only
- graph: aggregate CSV outputs
"""

import argparse
import csv
import logging
import os
import resource
import shutil
import shlex
import subprocess
import sys
import textwrap
import time
from dataclasses import dataclass, field
from itertools import zip_longest
from math import ceil
from pathlib import Path
import pandas as pd
import psutil
from natsort import natsorted
from tqdm import tqdm
import matplotlib.pyplot as plt
from matplotlib.backends.backend_pdf import PdfPages

from typing import Any, Dict, List, NoReturn, Optional, Sequence, TextIO, Tuple, cast


logger = logging.getLogger(__name__)
default_variants = ["no_opt", "exp_opt", "all_opt"]
default_primary_variant = "all_opt"

@dataclass
class BenchmarkRunnerConfig:
    benchmark_root: str
    csv_path: str
    case_limit: int = 0
    time_limit: float = 5
    memory_limit: float = 0.0
    dry_run: bool = False
    tag: str = ""
    log_path: str = "log"
    experiments: Optional[List[str]] = None
    exclude_experiments: Optional[List[str]] = None


@dataclass
class GraphConfig:
    prefix: str
    output_path: str = "."
    metadata_csv_path: Optional[str] = None
    search_root: str = "."
    variants: List[str] = field(default_factory=lambda: default_variants)
    primary_variant: Optional[str] = None
    figure_name: str = "benchmark.pdf"
    experiments: Optional[List[str]] = None
    exclude_experiments: Optional[List[str]] = None


@dataclass
class GenerateConfig:
    root: str = "/workspace"
    prefix: str = "benchmark-latest"
    variants: List[str] = field(default_factory=lambda: default_variants)
    dry_run: bool = False


@dataclass
class RunBenchmarkConfig:
    root: str = "/workspace"
    prefix: str = "benchmark-latest"
    variants: List[str] = field(default_factory=lambda: default_variants)
    case_limit: int = 0
    time_limit: float = 5
    memory_limit: float = 0.0
    dry_run: bool = False
    log_path: str = "log"
    metadata_csv_path: str = "benchmark-meta-data"
    output_path: str = "benchmark_result"
    primary_variant: Optional[str] = None
    figure_name: str = "benchmark.pdf"
    experiments: Optional[List[str]] = None
    exclude_experiments: Optional[List[str]] = None


def get_safe_memory_limit(ratio: float = 0.95) -> int:
    total = psutil.virtual_memory().total
    return int(total * ratio / 1024**3)


def create_dir_if_needed(dir_name: str) -> None:
    Path(dir_name).mkdir(parents=True, exist_ok=True)


def rename_csv_files_to_old(base_dir: Path) -> int:
    if not base_dir.exists() or not base_dir.is_dir():
        return 0

    renamed = 0
    for csv_path in sorted(base_dir.rglob("*.csv")):
        target = csv_path.with_suffix(f"{csv_path.suffix}.old")
        if target.exists():
            index = 1
            while True:
                candidate = csv_path.with_suffix(f"{csv_path.suffix}.old.{index}")
                if not candidate.exists():
                    target = candidate
                    break
                index += 1
        csv_path.rename(target)
        renamed += 1
    return renamed


def get_subdirs(directory: str) -> set[str]:
    return {
        sub
        for sub in os.listdir(directory)
        if os.path.isdir(os.path.join(directory, sub))
    }


def get_subdirs_in_native_order(directory: str) -> List[str]:
    return [
        sub
        for sub in os.listdir(directory)
        if os.path.isdir(os.path.join(directory, sub))
    ]


def limit_resources(memory_gb: float) -> None:
    max_bytes = int(memory_gb * 1024**3)
    resource.setrlimit(resource.RLIMIT_AS, (max_bytes, max_bytes))


def check_tool(tool_path: Path) -> None:
    if not tool_path.is_file():
        print(f"{tool_path.resolve()} does not exist. Make sure the tool exists.")
        sys.exit(1)


def fail(msg: str) -> NoReturn:
    raise SystemExit(f"Error: {msg}")


def validate_variants(variants: List[str]) -> List[str]:
    if not variants:
        fail("--variants cannot be empty")
    if len(set(variants)) != len(variants):
        fail("--variants contains duplicates")
    return variants


def validate_name_list(values: Optional[List[str]], arg_name: str) -> Optional[List[str]]:
    if values is None:
        return None
    if not values:
        fail(f"{arg_name} cannot be empty")
    if len(set(values)) != len(values):
        fail(f"{arg_name} contains duplicates")
    return values


def validate_experiments(experiments: Optional[List[str]]) -> Optional[List[str]]:
    return validate_name_list(experiments, "--experiments")


def validate_exclude_experiments(exclude_experiments: Optional[List[str]]) -> Optional[List[str]]:
    return validate_name_list(exclude_experiments, "--exclude_experiments")


def select_requested_items(available: Sequence[str], requested: Optional[Sequence[str]], arg_name: str = "--experiments") -> List[str]:
    available_set = set(available)
    if requested is None:
        return list(available)
    missing = [name for name in requested if name not in available_set]
    if missing:
        fail(f"invalid {arg_name} entries: {missing}; available: {sorted(available)}")
    return list(requested)


def exclude_requested_items(base: Sequence[str], available: Sequence[str], excluded: Optional[Sequence[str]]) -> List[str]:
    if excluded is None:
        return list(base)
    available_set = set(available)
    missing = [name for name in excluded if name not in available_set]
    if missing:
        fail(f"invalid --exclude_experiments entries: {missing}; available: {sorted(available)}")
    excluded_set = set(excluded)
    return [name for name in base if name not in excluded_set]


def resolve_experiment_selection(
    available: Sequence[str],
    experiments: Optional[Sequence[str]],
    exclude_experiments: Optional[Sequence[str]],
) -> List[str]:
    selected = select_requested_items(available, experiments, "--experiments")
    filtered = exclude_requested_items(selected, available, exclude_experiments)
    if not filtered:
        fail("no experiments left after applying --experiments/--exclude_experiments")
    return filtered


def resolve_primary_variant(variants: Sequence[str], primary_variant: Optional[str]) -> str:
    if not variants:
        fail("--variants cannot be empty")
    if primary_variant is not None:
        if primary_variant not in variants:
            fail(f"--primary_variant must be one of --variants: {list(variants)}")
        return primary_variant
    if default_primary_variant in variants:
        return default_primary_variant
    return variants[0]


def get_git_tags(repo_dir: Path) -> List[str]:
    if not repo_dir.is_dir():
        fail(f"git repository directory not found: {repo_dir}")

    try:
        result = subprocess.run(
            ["git", "tag", "--list"],
            cwd=str(repo_dir),
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
    except subprocess.CalledProcessError as exc:
        stderr = (exc.stderr or "").strip()
        fail(f"failed to list git tags in {repo_dir}: {stderr}")

    tags = [line.strip() for line in result.stdout.splitlines() if line.strip()]
    if not tags:
        fail(f"no git tags found in {repo_dir}")
    return tags


def validate_variants_against_git_tags(variants: List[str], fggs_repo_dir: Path) -> None:
    validate_variants(variants)
    tags = set(get_git_tags(fggs_repo_dir))
    invalid = [variant for variant in variants if variant not in tags]
    if invalid:
        sample = sorted(tags)
        preview = sample[:12]
        suffix = " ..." if len(sample) > 12 else ""
        fail(
            f"invalid variant(s): {invalid}; they must be existing git tags in {fggs_repo_dir}. "
            f"Available tags include: {preview}{suffix}"
        )


def validate_numeric_limits(case_limit: int, time_limit: float, memory_limit: float) -> None:
    if case_limit < 0:
        fail("--case_limit must be >= 0")
    if time_limit <= 0:
        fail("--time_limit must be > 0")
    if memory_limit <= 0:
        fail("--memory_limit must be > 0")


def validate_generate_config(opts: GenerateConfig) -> None:
    root = Path(opts.root).resolve()
    iso_dir = root / "iso"
    fggs_dir = root / "perpl" / "fggs"
    cases_script = iso_dir / "benchmark" / "case-generator" / "cases.rkt"

    if not root.is_dir():
        fail(f"root directory not found: {root}")
    if not iso_dir.is_dir():
        fail(f"iso directory not found: {iso_dir}")
    if not fggs_dir.is_dir():
        fail(f"fggs directory not found: {fggs_dir}")
    if not cases_script.is_file():
        fail(f"Racket generator script not found: {cases_script}")
    if not opts.prefix:
        fail("--prefix cannot be empty")

    if shutil.which("racket") is None:
        fail("'racket' not found in PATH")
    if shutil.which("git") is None:
        fail("'git' not found in PATH")

    validate_variants_against_git_tags(opts.variants, fggs_dir)


def validate_bench_config(opts: BenchmarkRunnerConfig) -> None:
    benchmark_root = Path(opts.benchmark_root).resolve()
    csv_path = Path(opts.csv_path)

    if not benchmark_root.is_dir():
        fail(f"benchmark_root directory not found: {benchmark_root}")
    if not opts.log_path:
        fail("--log cannot be empty")

    validate_experiments(opts.experiments)
    validate_exclude_experiments(opts.exclude_experiments)
    validate_numeric_limits(opts.case_limit, opts.time_limit, opts.memory_limit)

    iso_root = benchmark_root.parent
    workspace_root = iso_root.parent
    perpl_root = workspace_root / "perpl"
    fgg_root = perpl_root / "fggs"

    if not (iso_root / "iso-exe").is_file():
        fail(f"missing tool: {iso_root / 'iso-exe'}")
    if not (perpl_root / "perplc").is_file():
        fail(f"missing tool: {perpl_root / 'perplc'}")
    if not (fgg_root / "bin" / "sum_product.py").is_file():
        fail(f"missing tool: {fgg_root / 'bin' / 'sum_product.py'}")

    csv_parent = csv_path if csv_path.suffix == "" else csv_path.parent
    if str(csv_parent) and not csv_parent.exists():
        # creation is handled later; this is a soft check to keep semantics clear
        parent_parent = csv_parent.parent
        if not parent_parent.exists():
            fail(f"output parent directory does not exist: {parent_parent}")

    available = get_subdirs_in_native_order(str(benchmark_root))
    if not available:
        fail(f"no benchmark suites found in {benchmark_root}")
    resolve_experiment_selection(available, opts.experiments, opts.exclude_experiments)


def validate_graph_config(opts: GraphConfig) -> None:
    search_root = Path(opts.search_root).resolve()
    output_path = Path(opts.output_path)

    if not opts.prefix:
        fail("prefix cannot be empty")
    if not search_root.is_dir():
        fail(f"search_root directory not found: {search_root}")
    if opts.metadata_csv_path:
        meta_path = Path(opts.metadata_csv_path)
        if not meta_path.is_dir():
            fail(f"metadata directory not found: {meta_path}")

    matches = [path for path in search_root.iterdir() if path.is_dir() and path.name.startswith(opts.prefix)]
    if not matches:
        fail(f"no directories found in {search_root} with prefix '{opts.prefix}'")

    out_parent = output_path if output_path.suffix == "" else output_path.parent
    if str(out_parent) and not out_parent.exists() and not out_parent.parent.exists():
        fail(f"output parent directory does not exist: {out_parent.parent}")

    if not opts.figure_name:
        fail("--figure_name cannot be empty")

    validate_variants(opts.variants)
    resolve_primary_variant(opts.variants, opts.primary_variant)
    validate_experiments(opts.experiments)
    validate_exclude_experiments(opts.exclude_experiments)
    available_tags = get_subdirs_in_native_order(str(matches[0]))
    if not available_tags:
        fail(f"no experiment tags found in {matches[0]}")
    resolve_experiment_selection(available_tags, opts.experiments, opts.exclude_experiments)


def validate_run_config(opts: RunBenchmarkConfig) -> None:
    root = Path(opts.root).resolve()
    iso_dir = root / "iso"
    fggs_dir = root / "perpl" / "fggs"

    if not root.is_dir():
        fail(f"root directory not found: {root}")
    if not iso_dir.is_dir():
        fail(f"iso directory not found: {iso_dir}")
    if not fggs_dir.is_dir():
        fail(f"fggs directory not found: {fggs_dir}")
    if not opts.prefix:
        fail("--prefix cannot be empty")

    validate_experiments(opts.experiments)
    validate_exclude_experiments(opts.exclude_experiments)
    validate_numeric_limits(opts.case_limit, opts.time_limit, opts.memory_limit)

    if not opts.figure_name:
        fail("--figure_name cannot be empty")

    if shutil.which("git") is None:
        fail("'git' not found in PATH")

    validate_variants_against_git_tags(opts.variants, fggs_dir)

    # run mode relies on generation mode prerequisites
    validate_generate_config(
        GenerateConfig(root=opts.root, prefix=opts.prefix, variants=opts.variants, dry_run=opts.dry_run)
    )

def discover_suites(
    benchmark_root: str,
    experiments: Optional[Sequence[str]] = None,
    exclude_experiments: Optional[Sequence[str]] = None,
) -> List[str]:
    suites = get_subdirs_in_native_order(benchmark_root)
    if not suites:
        print(f"Error: No benchmark suites found in {benchmark_root}")
        sys.exit(1)
    return resolve_experiment_selection(suites, experiments, exclude_experiments)


def check_tools_for_benchmark(opts: BenchmarkRunnerConfig) -> None:
    benchmark_root = Path(opts.benchmark_root).resolve()
    iso_root = benchmark_root.parent
    workspace_root = iso_root.parent
    perpl_root = workspace_root / "perpl"
    fgg_root = perpl_root / "fggs"

    check_tool(iso_root / "iso-exe")
    check_tool(perpl_root / "perplc")
    check_tool(fgg_root / "bin" / "sum_product.py")


def run_command(
    dir_path: Path,
    isuffix: str,
    osuffix: str,
    cmd: List[str],
    result_dir: Path,
    iopt: str,
    oopt: str,
    tag: str,
    opts: BenchmarkRunnerConfig,
) -> List[float]:
    timeout_seconds = opts.time_limit * 60
    create_dir_if_needed(str(result_dir))

    files = natsorted(Path(dir_path).rglob(f"*{isuffix}"), key=lambda p: p.name)
    if opts.case_limit > 0:
        files = files[: opts.case_limit]

    short_tag = textwrap.shorten(tag, width=15)
    time_data: List[float] = []

    if not files and opts.dry_run:
        tqdm.write(f'Skip running command {cmd}')

    for ifile in tqdm(
        files,
        desc=short_tag,
        bar_format="{desc:<10} |{bar}| {n_fmt}/{total_fmt} [{elapsed}<{remaining}]",
    ):
        ofile = ifile.stem + osuffix
        output_path = result_dir / ofile

        full_cmd = list(cmd)
        if iopt:
            full_cmd.append(iopt)
        full_cmd.append(str(ifile))

        out_port: TextIO
        if oopt == ">":
            out_port = open(output_path, "w")
        elif oopt:
            full_cmd.append(oopt)
            full_cmd.append(str(output_path))
            out_port = cast(TextIO, sys.stdout)
        else:
            out_port = cast(TextIO, sys.stdout)

        pretty_cmd = shlex.join(full_cmd)
        if oopt == ">":
            pretty_cmd = f"{pretty_cmd} > {output_path}"
        logger.info(pretty_cmd)

        normal = True
        time_diff = 0.0
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
                    preexec_fn=lambda: limit_resources(opts.memory_limit),
                )
                normal = result.returncode == 0
                if result.stderr:
                    logger.error("Subprocess stderr:\n%s", result.stderr.decode("utf-8"))
            except subprocess.TimeoutExpired:
                tqdm.write(f"[TIMEOUT] {shlex.join(full_cmd)}")
                logger.info("[EXCEPTION] %s", shlex.join(full_cmd))
                normal = False
            except Exception as exc:
                tqdm.write(f"[EXCEPTION] {exc}")
                logger.info("[EXCEPTION] %s", exc)
                normal = False
            time_diff = time.time() - start

        if oopt == ">":
            out_port.close()

        if not normal:
            tqdm.write(f"Stop at {ifile}", file=sys.stderr)
            logger.info("Stop at %s", ifile)
            break

        time_data.append(time_diff)

    return time_data


def run_single_suite(suite_name: str, opts: BenchmarkRunnerConfig) -> None:
    benchmark_root = Path(opts.benchmark_root).resolve()
    iso_root = benchmark_root.parent
    workspace_root = iso_root.parent
    perpl_root = workspace_root / "perpl"
    fgg_root = perpl_root / "fggs"

    suite_root = benchmark_root / suite_name
    iso_suite_dir = suite_root / "iso"
    qiskit_suite_dir = suite_root / "qiskit"
    qsim_suite_dir = suite_root / "qsim"
    qtorch_suite_dir = suite_root / "qtorch"

    ppl_dir = suite_root / "ppl"
    json_dir = suite_root / "json"
    iso_result_dir = suite_root / "iso-text"
    qiskit_result_dir = suite_root / "qiskit-text"
    iso_fgg_dir = suite_root / "iso-fgg"
    iso_fgg_result_dir = suite_root / "iso-fgg-text"
    qsim_result_dir = suite_root / "qsim-text"
    qtorch_result_dir = suite_root / "qtorch-text"

    tqdm.write(f"Running benchmark {suite_name}")
    logger.info("Running benchmark %s", suite_name)

    row_tag = f"{suite_name}-{opts.tag}"
    tags = [
        f"{row_tag}:iso-to-perpl",
        f"{row_tag}:perpl-to-fgg",
        f"{row_tag}:iso-simulation",
        f"{row_tag}:iso-to-fgg",
        f"{row_tag}:iso-fgg-simulation",
        f"{row_tag}:qiskit-simulation",
        f"{row_tag}:qsim-simulation",
        f"{row_tag}:qtorch-simulation",
    ]

    iso_to_perpl = run_command(
        iso_suite_dir,
        ".iso",
        ".ppl",
        [str(iso_root / "iso-exe"), "perpl"],
        ppl_dir,
        "",
        "-o",
        tags[0],
        opts,
    )

    perpl_to_fgg = run_command(
        ppl_dir,
        ".ppl",
        ".json",
        [str(perpl_root / "perplc")],
        json_dir,
        "-s",
        ">",
        tags[1],
        opts,
    )

    iso_simulation = run_command(
        json_dir,
        ".json",
        "-iso.txt",
        ["python", str(fgg_root / "bin" / "sum_product.py")],
        iso_result_dir,
        "-d",
        ">",
        tags[2],
        opts,
    )

    iso_to_fgg = run_command(
        iso_suite_dir,
        ".iso",
        "-iso-fgg.json",
        [str(iso_root / "iso-exe"), "fgg"],
        iso_fgg_dir,
        "-c",
        "-o",
        tags[3],
        opts,
    )

    iso_fgg_simulation = run_command(
        iso_fgg_dir,
        ".json",
        "-iso.txt",
        ["python", str(fgg_root / "bin" / "sum_product.py")],
        iso_fgg_result_dir,
        "-d",
        ">",
        tags[4],
        opts,
    )

    qiskit_simulation = run_command(
        qiskit_suite_dir,
        ".py",
        "-qiskit.txt",
        ["python"],
        qiskit_result_dir,
        "",
        ">",
        tags[5],
        opts,
    )

    qsim_simulation = run_command(
        qsim_suite_dir,
        ".py",
        "-qsim.txt",
        ["python"],
        qsim_result_dir,
        "",
        ">",
        tags[6],
        opts,
    )

    qtorch_simulation = run_command(
        qtorch_suite_dir,
        ".sim",
        "-qtorch.txt",
        ["qtorch"],
        qtorch_result_dir,
        "",
        ">",
        tags[7],
        opts,
    )

    if not opts.dry_run:
        create_dir_if_needed(opts.csv_path)
        output_csv = Path(opts.csv_path) / f"{suite_name}-{opts.tag}-{time.strftime('%Y-%m-%d_%H-%M-%S')}.csv"
        with open(output_csv, "w", newline="") as handle:
            writer = csv.writer(handle)
            writer.writerow(tags)
            for row in zip_longest(
                iso_to_perpl,
                perpl_to_fgg,
                iso_simulation,
                iso_to_fgg,
                iso_fgg_simulation,
                qiskit_simulation,
                qsim_simulation,
                qtorch_simulation,
                fillvalue="",
            ):
                writer.writerow(row)


def run_bench_mode(opts: BenchmarkRunnerConfig) -> None:
    create_dir_if_needed(opts.csv_path)

    if not opts.dry_run:
        rename_roots = {
            Path(opts.benchmark_root).resolve(),
            Path(opts.csv_path).resolve(),
        }
        renamed_total = 0
        for root in rename_roots:
            renamed_total += rename_csv_files_to_old(root)
        if renamed_total:
            print(f"Renamed {renamed_total} existing CSV file(s) to .csv.old for bench run")

    log_dir = Path(opts.log_path).parent
    if str(log_dir) not in ("", "."):
        create_dir_if_needed(str(log_dir))

    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s.%(msecs)03d %(levelname)-8s %(message)s",
        datefmt="%Y-%m-%d_%H:%M:%S",
        filename=f"{opts.log_path}-{time.strftime('%Y-%m-%d_%H-%M-%S')}.log",
        filemode="w",
    )

    check_tools_for_benchmark(opts)
    for suite in discover_suites(opts.benchmark_root, opts.experiments, opts.exclude_experiments):
        run_single_suite(suite, opts)


def discover_tags(prefix: str, search_root: str) -> List[str]:
    search_root_path = Path(search_root)
    target_dirs = sorted(
        path for path in search_root_path.iterdir() if path.is_dir() and path.name.startswith(prefix)
    )

    if not target_dirs:
        raise SystemExit(f"Error: No folders found with prefix {prefix}")

    master_tags_ordered = get_subdirs_in_native_order(str(target_dirs[0]))
    master_tags = set(master_tags_ordered)
    if not master_tags:
        raise SystemExit(f"Error: No tags found in {target_dirs[0]}")

    mismatched = False
    for target_dir in target_dirs[1:]:
        current_tags = get_subdirs(str(target_dir))
        if current_tags != master_tags:
            mismatched = True
            missing = master_tags - current_tags
            extra = current_tags - master_tags
            print(f"Structure mismatch in {target_dir}")
            if missing:
                print(f"Missing: {missing}")
            if extra:
                print(f"Extra: {extra}")

    if mismatched:
        raise SystemExit(1)

    print(f"Verification successful. Targets: {len(target_dirs)}, Tags: {len(master_tags)}")
    return master_tags_ordered


def find_files_by_prefix_and_tag(prefix: str, tag: str, search_root: str) -> List[Path]:
    search_root_path = Path(search_root)
    target_dirs = [
        path for path in search_root_path.iterdir() if path.is_dir() and path.name.startswith(prefix)
    ]
    if not target_dirs:
        raise SystemExit(f"Error: No directories found with prefix {prefix}")

    matched_files: List[Path] = []
    for directory in target_dirs:
        for file_path in directory.iterdir():
            if file_path.is_file() and file_path.name.startswith(tag) and file_path.suffix == ".csv":
                matched_files.append(file_path)

    if not matched_files:
        raise SystemExit(f"Error: No CSV files matched tag {tag}")

    print(f"Found {len(matched_files)} files across {len(target_dirs)} directories")
    return sorted(matched_files)


def combine_graph(
    tag: str,
    files: List[Path],
    avg_cols: List[str],
    add_cols: List[List[str]],
    mul_cols: List[List[str]],
    meta_path: Optional[str],
    out_name: Path,
) -> None:
    dataframes = [pd.read_csv(csv_file) for csv_file in files]
    dataframe = pd.concat(dataframes, axis=1)

    if meta_path:
        meta_file = Path(meta_path) / f"{tag}.csv"
        if meta_file.is_file():
            print(f"Use extra CSV file {meta_file}")
            extra_df = pd.read_csv(meta_file)
            dataframe = pd.concat([extra_df, dataframe], axis=1)

    for avg_col in avg_cols:
        cols_to_average = [column for column in dataframe.columns if column.endswith(avg_col)]
        dataframe[f"{tag}-avg:{avg_col}"] = dataframe[cols_to_average].mean(axis=1, skipna=True)

    for add_col in add_cols:
        dest = add_col[0]
        src = add_col[1:]
        dataframe[dest] = dataframe[src].sum(axis=1, min_count=len(src))

    for mul_col in mul_cols:
        dest = mul_col[0]
        src = mul_col[1:]
        dataframe[dest] = (2 ** dataframe[src[1]]) * dataframe[src[0]]

    create_dir_if_needed(str(out_name.parent))
    print(f"Write to {out_name}")
    dataframe.to_csv(out_name, index=False)


def run_graph_mode(opts: GraphConfig) -> None:
    create_dir_if_needed(opts.output_path)
    discovered_tags = discover_tags(opts.prefix, opts.search_root)
    tags = resolve_experiment_selection(discovered_tags, opts.experiments, opts.exclude_experiments)
    primary_variant = resolve_primary_variant(opts.variants, opts.primary_variant)

    for tag in tags:
        print(f"Process {tag}")
        files = find_files_by_prefix_and_tag(opts.prefix, tag, opts.search_root)

        avg_cols = [
            "qiskit-simulation",
            "qsim-simulation",
            "qtorch-simulation",
            "iso-to-perpl",
            "perpl-to-fgg",
            "iso-to-fgg",
        ]
        add_cols = [
            [
                f"{tag}-avg:iso-perpl-fgg",
                f"{tag}-avg:perpl-to-fgg",
                f"{tag}-avg:iso-to-fgg"
            ],
        ]
        for variant in opts.variants:
            add_cols.append([
                f"{tag}-{variant}:iso-perpl-fgg-total",
                f"{tag}-{variant}:iso-simulation",
                f"{tag}-{variant}:iso-to-perpl",
                f"{tag}-{variant}:perpl-to-fgg"
            ])
            add_cols.append([
                f"{tag}-{variant}:iso-fgg-total",
                f"{tag}-{variant}:iso-fgg-simulation",
                f"{tag}-{variant}:iso-to-fgg"
            ])

        mul_cols = [
            [
                f"{tag}-avg:qtorch-simulation-full",
                f"{tag}-avg:qtorch-simulation",
                "qubit-number"]
        ]

        combine_graph(
            tag=tag,
            files=files,
            avg_cols=avg_cols,
            add_cols=add_cols,
            mul_cols=mul_cols,
            meta_path=opts.metadata_csv_path,
            out_name=Path(opts.output_path) / f"{tag}.csv",
        )

    output_dir = Path(opts.output_path)
    run_embedded_figure_generation(
        data_dir=output_dir,
        figure_name=opts.figure_name,
        variants=opts.variants,
        primary_variant=primary_variant,
        experiments=tags,
    )



def _generate_plot_title_overrides(experiments: Sequence[str]) -> Dict[str, str]:
    def humanize(name: str) -> str:
        words = name.replace("-", " ").split()
        if not words:
            return name

        acronyms = {"qft", "mcx"}
        titled: List[str] = []
        for word in words:
            if word.lower() in acronyms:
                titled.append(word.upper())
            else:
                titled.append(word.capitalize())
        return " ".join(titled)

    return {name: humanize(name) for name in experiments}


def _plot_build_fig1_series(primary_variant: str) -> List[Tuple[str, str, str]]:
    return [
        (f"FGG simulation ({primary_variant})", f"{{name}}-{primary_variant}:iso-fgg-total", "tab:red"),
        (f"FGG simulation through PERPL ({primary_variant})", f"{{name}}-{primary_variant}:iso-perpl-fgg-total", "tab:orange"),
        ("Qiskit", "{name}-avg:qiskit-simulation", "tab:green"),
        ("qsim", "{name}-avg:qsim-simulation", "tab:blue"),
        ("qTorch", "{name}-avg:qtorch-simulation-full", "tab:purple"),
    ]

PLOT_VARIANT_COLOR_PAIRS: List[Tuple[str, str]] = [
    ("tab:red", "tab:orange"),
    ("tab:blue", "tab:cyan"),
    ("gold", "olive"),
    ("tab:purple", "tab:green"),
    ("tab:pink", "tab:brown"),
    ("tab:gray", "black"),
]


def _plot_experiment_specs(experiments: Sequence[str]) -> List[Tuple[str, str, str]]:
    if not experiments:
        fail("at least one experiment is required to generate figures")
    title_overrides = _generate_plot_title_overrides(experiments)
    return [(name, title_overrides[name], f"{name}.csv") for name in experiments]


def _plot_chunk_specs(specs: Sequence[Tuple[str, str, str]], size: int = 6) -> List[List[Tuple[str, str, str]]]:
    return [list(specs[i:i + size]) for i in range(0, len(specs), size)]


def _plot_make_page_axes(count: int):
    rows = max(1, (count + 1) // 2)
    fig, axes = plt.subplots(rows, 2, figsize=(12, 4 * rows), constrained_layout=False)
    if hasattr(axes, "flat"):
        axes_list = list(cast(Any, axes).flat)
    else:
        axes_list = [axes]
    return fig, axes_list


def _plot_build_fig2_series(variants: Sequence[str]) -> List[Tuple[str, str, str]]:
    series: List[Tuple[str, str, str]] = []

    for idx, variant in enumerate(variants):
        solver_color, pipeline_color = PLOT_VARIANT_COLOR_PAIRS[idx % len(PLOT_VARIANT_COLOR_PAIRS)]
        series.append((f"FGG solver: {variant}", f"{{name}}-{variant}:iso-fgg-simulation", solver_color))
        series.append((f"PERPL pipeline: {variant}", f"{{name}}-{variant}:iso-simulation", pipeline_color))

    series.append(("Compile ISO->FGG", "{name}-avg:iso-to-fgg", "tab:pink"))
    series.append(("Compile via PERPL", "{name}-avg:iso-perpl-fgg", "tab:brown"))
    return series


def _plot_parse_float(value: str) -> float:
    text = value.strip() if value is not None else ""
    if text == "":
        return float("nan")
    try:
        return float(text)
    except ValueError:
        return float("nan")


def _plot_load_csv_columns(path: Path) -> Dict[str, List[float]]:
    with path.open("r", encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        fieldnames = reader.fieldnames
        if fieldnames is None:
            fail(f"CSV has no header: {path}")
        columns: Dict[str, List[float]] = {name: [] for name in fieldnames}
        for row in reader:
            for name in fieldnames:
                columns[name].append(_plot_parse_float(row.get(name, "")))
    return columns


def _plot_require_columns(columns: Dict[str, List[float]], names: Sequence[str], path: Path) -> None:
    missing = [name for name in names if name not in columns]
    if missing:
        fail(f"Missing columns in {path}: {missing}")


def _plot_draw_series(ax, x: List[float], columns: Dict[str, List[float]], benchmark_name: str, series_def):
    for label, col_template, color in series_def:
        col = col_template.format(name=benchmark_name)
        ax.plot(x, columns[col], label=label, color=color, linewidth=1.2, marker="o", markersize=2.8)


def _plot_make_figure_1_page(data_dir: Path, specs: Sequence[Tuple[str, str, str]], primary_variant: str):
    fig, axes_list = _plot_make_page_axes(len(specs))
    legend_handles: List[Any] = []
    legend_labels: List[str] = []
    fig1_series = _plot_build_fig1_series(primary_variant)

    for idx, (name, title, csv_name) in enumerate(specs):
        ax = axes_list[idx]
        ax2 = ax.twinx()

        path = data_dir / csv_name
        columns = _plot_load_csv_columns(path)

        required = ["qubit-number", "gate-number"] + [tmpl.format(name=name) for _, tmpl, _ in fig1_series]
        _plot_require_columns(columns, required, path)

        x = columns["qubit-number"]
        _plot_draw_series(ax, x, columns, name, fig1_series)

        ax2.plot(x, columns["gate-number"], label="Number of gates", color="gray", linestyle=":", linewidth=1.4)

        col = idx % 2
        ax.set_yscale("log")
        ax2.set_yscale("log")
        ax.set_xlabel("Number of qubits")
        if col == 0:
            ax.set_ylabel("Running time (seconds)")
        if col == 1:
            ax2.set_ylabel("Number of gates")
        ax.set_title(title)
        ax.grid(True, which="both", alpha=0.15)

        if not legend_handles:
            h1, l1 = ax.get_legend_handles_labels()
            h2, l2 = ax2.get_legend_handles_labels()
            legend_handles = h1 + h2
            legend_labels = l1 + l2

    for ax in axes_list[len(specs):]:
        ax.axis("off")

    fig.suptitle("Experiment results, comparing all simulators.", fontsize=12)
    fig.tight_layout(rect=(0.02, 0.14, 0.98, 0.96))
    if legend_handles and legend_labels:
        fig.legend(
            legend_handles,
            legend_labels,
            loc="lower center",
            bbox_to_anchor=(0.5, 0.025),
            ncol=3,
            frameon=False)
    return fig


def _plot_make_figure_2_page(data_dir: Path, variants: Sequence[str], specs: Sequence[Tuple[str, str, str]]):
    fig, axes_list = _plot_make_page_axes(len(specs))
    legend_handles: List[Any] = []
    legend_labels: List[str] = []
    fig2_series = _plot_build_fig2_series(variants)

    for idx, (name, title, csv_name) in enumerate(specs):
        ax = axes_list[idx]

        path = data_dir / csv_name
        columns = _plot_load_csv_columns(path)

        required = ["qubit-number"] + [tmpl.format(name=name) for _, tmpl, _ in fig2_series]
        _plot_require_columns(columns, required, path)

        x = columns["qubit-number"]
        _plot_draw_series(ax, x, columns, name, fig2_series)

        col = idx % 2
        ax.set_yscale("log")
        ax.set_xlabel("Number of qubits")
        if col == 0:
            ax.set_ylabel("Running time (seconds)")
        ax.set_title(title)
        ax.grid(True, which="both", alpha=0.15)

        if not legend_handles:
            legend_handles, legend_labels = ax.get_legend_handles_labels()

    for ax in axes_list[len(specs):]:
        ax.axis("off")

    fig.suptitle(
        "Simulation and compilation times of our FGG-based simulators, comparing different sets of optimizations.",
        fontsize=12,
    )
    if legend_handles and legend_labels:
        subplot_count = len(specs)
        legend_ncol = 2
        bottom = -0.15 * ceil(subplot_count / 2.0) + 0.57
        fig.tight_layout(rect=(0.02, bottom, 0.98, 0.96))
        fig.legend(
            legend_handles,
            legend_labels,
            loc="lower center",
            bbox_to_anchor=(0.5, 0.02),
            ncol=legend_ncol,
            frameon=False,
        )
    else:
        fig.tight_layout(rect=(0.02, 0.12, 0.98, 0.96))
    return fig


def run_embedded_figure_generation(
    data_dir: Path,
    figure_name: str,
    variants: Sequence[str],
    primary_variant: str,
    experiments: Sequence[str],
) -> None:
    specs = _plot_experiment_specs(experiments)
    chunks = _plot_chunk_specs(specs, size=6)

    combined_path = Path(figure_name)
    if not combined_path.is_absolute():
        combined_path = data_dir / combined_path
    combined_path.parent.mkdir(parents=True, exist_ok=True)

    with PdfPages(combined_path) as pdf:
        for chunk in chunks:
            fig = _plot_make_figure_1_page(data_dir, chunk, primary_variant)
            pdf.savefig(fig)
            plt.close(fig)
        for chunk in chunks:
            fig = _plot_make_figure_2_page(data_dir, variants, chunk)
            pdf.savefig(fig)
            plt.close(fig)

    print(f"Wrote: {combined_path}")


def run_process(cmd: List[str], cwd: Optional[str] = None, dry_run: bool = False) -> None:
    printable = shlex.join(cmd)
    print(f"Running: {printable} (cwd={cwd})")
    if not dry_run:
        subprocess.run(cmd, check=True, cwd=cwd)


def run_generate_mode(opts: GenerateConfig) -> None:
    root = os.path.abspath(opts.root)
    iso_dir = os.path.join(root, "iso")

    for tag in opts.variants:
        benchmark_dir_name = f"{opts.prefix}-{tag}"
        run_process(
            ["racket", "benchmark/case-generator/cases.rkt", "-d", benchmark_dir_name],
            cwd=iso_dir,
            dry_run=opts.dry_run,
        )


def run_full_mode(opts: RunBenchmarkConfig) -> None:
    root = os.path.abspath(opts.root)
    iso_dir = os.path.join(root, "iso")
    fggs_dir = os.path.join(root, "perpl", "fggs")

    for tag in opts.variants:
        benchmark_dir_name = f"{opts.prefix}-{tag}"
        benchmark_root = os.path.join(iso_dir, benchmark_dir_name)

        run_process(["git", "restore", "--staged", "--", "."], cwd=fggs_dir, dry_run=opts.dry_run)
        run_process(["git", "checkout", "--", "."], cwd=fggs_dir, dry_run=opts.dry_run)
        run_process(["git", "checkout", tag], cwd=fggs_dir, dry_run=opts.dry_run)
        run_generate_mode(GenerateConfig(root=opts.root, prefix=opts.prefix, variants=[tag], dry_run=opts.dry_run))

        bench_opts = BenchmarkRunnerConfig(
            benchmark_root=benchmark_root,
            csv_path=benchmark_root,
            case_limit=opts.case_limit,
            time_limit=opts.time_limit,
            memory_limit=opts.memory_limit,
            dry_run=opts.dry_run,
            tag=tag,
            log_path=os.path.join(benchmark_root, f"{opts.log_path}-{tag}"),
            experiments=opts.experiments,
            exclude_experiments=opts.exclude_experiments,
        )
        validate_bench_config(bench_opts)
        run_bench_mode(bench_opts)

    if opts.dry_run:
        print("Skip graph generation during dry run")
    else:
        graph_output_dir = Path(iso_dir) / opts.output_path
        renamed = rename_csv_files_to_old(graph_output_dir)
        if renamed:
            print(f"Renamed {renamed} existing CSV file(s) to .csv.old under {graph_output_dir}")

        graph_opts = GraphConfig(
            prefix=opts.prefix,
            output_path=os.path.join(iso_dir, opts.output_path),
            metadata_csv_path=os.path.join(iso_dir, opts.metadata_csv_path),
            search_root=iso_dir,
            variants=opts.variants,
            primary_variant=opts.primary_variant,
            figure_name=opts.figure_name,
            experiments=opts.experiments,
            exclude_experiments=opts.exclude_experiments,
        )
        validate_graph_config(graph_opts)
        run_graph_mode(graph_opts)


def add_common_run_flags(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--case_limit", type=int, default=0, help="Limit case count. Zero means no limit")
    parser.add_argument("-d", "--dry_run", action="store_true", help="Print commands without executing")
    parser.add_argument("-t", "--time_limit", type=float, default=5, metavar="<minutes>", help="Time limit per command in minutes")
    parser.add_argument("-m", "--memory_limit", type=float, default=get_safe_memory_limit(), metavar="<gigabytes>", help="Memory limit per command in GB")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Benchmark CLI",
                                     formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    subparsers = parser.add_subparsers(dest="mode", required=True)

    run_parser = subparsers.add_parser("run", help="Run full benchmark pipeline",
                                       formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    run_parser.add_argument("--root", default="/workspace", help="Workspace root that contains iso and perpl")
    run_parser.add_argument("--prefix", default="benchmark-latest", help="Prefix for generated benchmark directories")
    run_parser.add_argument("--variants", nargs="+", default=default_variants, help="Optimization variants")
    run_parser.add_argument("--primary_variant", default=None,
                            help=f"Variant used by figure 1 optimized lines, default to {default_primary_variant} "
                            "if it is in --variants,"
                            "otherwise default to the first option in --variants.")
    add_common_run_flags(run_parser)
    run_parser.add_argument("--log", default="log", dest="log_path", help="Base log name")
    run_parser.add_argument("-o", "--output_path", default="benchmark_result", dest="output_path", help="Graph CSV output directory")
    run_parser.add_argument("--meta_path", default="benchmark-meta-data", dest="metadata_csv_path",
                            help="Optional directory with extra metadata CSV files")
    run_parser.add_argument("--figure_name", default="benchmark.pdf",
                            help="Benchmark PDF output name. The PDF will be put into --output_path.")
    run_parser.add_argument("--experiments", nargs="+", default=None, help="Experiment names to include")
    run_parser.add_argument("--exclude_experiments", nargs="+", default=None, help="Experiment names to exclude")

    generate_parser = subparsers.add_parser("generate", help="Generate benchmark cases using Racket only",
                                            formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    generate_parser.add_argument("--root", default="/workspace", help="Workspace root that contains iso")
    generate_parser.add_argument("--prefix", default="benchmark-latest", help="Prefix for generated benchmark directories")
    generate_parser.add_argument("--variants", nargs="+", default=default_variants, help="Optimization variants")
    generate_parser.add_argument("-d", "--dry_run", action="store_true", help="Print commands without executing")

    bench_parser = subparsers.add_parser("bench", help="Run benchmark execution only",
                                         formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    bench_parser.add_argument("--benchmark_root", required=True, type=str, help="Root directory for one generated benchmark variant")
    bench_parser.add_argument("--csv_path", required=True, type=str, help="Output directory for benchmark CSV reports")
    add_common_run_flags(bench_parser)
    bench_parser.add_argument("--tag", default="", help="Tag used in benchmark CSV headers")
    bench_parser.add_argument("--log", default="log", dest="log_path", help="Base log name")
    bench_parser.add_argument("--experiments", nargs="+", default=None, help="Experiment names to include")
    bench_parser.add_argument("--exclude_experiments", nargs="+", default=None, help="Experiment names to exclude")

    graph_parser = subparsers.add_parser("graph", help="Aggregate benchmark CSV outputs",
                                         formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    graph_parser.add_argument("--prefix", required=True, type=str, help="Prefix for benchmark directories")
    graph_parser.add_argument("-o", "--output_path", default=".", help="Graph CSV output directory")
    graph_parser.add_argument("--meta_path", default=None, dest="metadata_csv_path",
                              help="Optional directory with extra metadata CSV files")
    graph_parser.add_argument("--search_root", type=str, default=".", help="Directory whose children are searched")
    graph_parser.add_argument("--variants", nargs="+", default=default_variants,
                              help="Optimization variants")
    graph_parser.add_argument("--primary_variant", default=None,
                              help=f"Variant used by figure 1 optimized lines, default to {default_primary_variant}"
                              " if it is in --variants,"
                              "otherwise default to the first option in --variants.")
    graph_parser.add_argument("--figure_name", type=str, default="benchmark.pdf",
                              help="Benchmark PDF output name. The PDF will be put into --output_path.")
    graph_parser.add_argument("--experiments", nargs="+", default=None, help="Experiment names to include")
    graph_parser.add_argument("--exclude_experiments", nargs="+", default=None, help="Experiment names to exclude")

    return parser


def main() -> None:
    args = build_parser().parse_args()

    if args.mode == "run":
        run_config = RunBenchmarkConfig(
            root=args.root,
            prefix=args.prefix,
            variants=args.variants,
            primary_variant=args.primary_variant,
            case_limit=args.case_limit,
            time_limit=args.time_limit,
            memory_limit=args.memory_limit,
            dry_run=args.dry_run,
            log_path=args.log_path,
            metadata_csv_path=args.metadata_csv_path,
            output_path=args.output_path,
            figure_name=args.figure_name,
            experiments=args.experiments,
            exclude_experiments=args.exclude_experiments,
        )
        validate_run_config(run_config)
        run_full_mode(run_config)

    elif args.mode == "generate":
        generate_config = GenerateConfig(
            root=args.root,
            prefix=args.prefix,
            variants=args.variants,
            dry_run=args.dry_run,
        )
        validate_generate_config(generate_config)
        run_generate_mode(generate_config)

    elif args.mode == "bench":
        bench_config = BenchmarkRunnerConfig(
            benchmark_root=args.benchmark_root,
            csv_path=args.csv_path,
            case_limit=args.case_limit,
            time_limit=args.time_limit,
            memory_limit=args.memory_limit,
            dry_run=args.dry_run,
            tag=args.tag,
            log_path=args.log_path,
            experiments=args.experiments,
            exclude_experiments=args.exclude_experiments,
        )
        validate_bench_config(bench_config)
        run_bench_mode(bench_config)

    elif args.mode == "graph":
        graph_config = GraphConfig(
            prefix=args.prefix,
            output_path=args.output_path,
            metadata_csv_path=args.metadata_csv_path,
            search_root=args.search_root,
            variants=args.variants,
            primary_variant=args.primary_variant,
            figure_name=args.figure_name,
            experiments=args.experiments,
            exclude_experiments=args.exclude_experiments,
        )
        validate_graph_config(graph_config)
        run_graph_mode(graph_config)

    else:
        raise SystemExit(f"Unknown mode {args.mode}: check available modes with -h")

if __name__ == "__main__":
    main()
