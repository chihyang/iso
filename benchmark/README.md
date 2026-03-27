ISO benchmark
=======

This is the documentation for the ISO benchmark.

# Quick start

## Pull a docker image

``` shell
docker pull chihyanghsin/iso-benchmark:latest-cpu
```

## Run a docker container

``` shell
docker run -it --rm -v $(pwd):/benchmark/result chihyanghsin/iso-benchmark:latest-cpu /bin/bash
```

The command above will mount your current directory `$(pwd)` as `/benchmark/result` within the docker container.
The benchmark scripts you run below will put the results into this directory.

## Check existing results

Within the docker container, you can check the existing benchmark results.
Enter the directory `result_2026_03_14`:

``` shell
cd /benchmark/result/result_2026_03_14
```

You can see the following files:

| File                                   | Explanation                           |
|----------------------------------------|---------------------------------------|
| `benchmark.pdf`                        | The existing benchmark result figures |
| `benchmark.tex`                        | The source code of the figures        |
| `deutsch-jozsa-is-even-simplified.csv` | Benchmark data of the Deutsch-Jozsa   |
| `deutsch-jozsa-to-zero-simplified.csv` | Benchmark data of the Deutsch-Jozsa   |
| `grover.csv`                           | Benchmark data of Grover's            |
| `had-last-qubit.csv`                   | Benchmark data of Hadamard            |
| `mcx.csv`                              | Benchmark data of Multiple-Control-X  |
| `qft.csv`                              | Benchmark data of QFT                 |
| `simon.csv`                            | Benchmark data of Simon's             |

If you want to reproduce the data above, you can choose to run either the small benchmark script to get a partial result, or the full benchmark script to get the complete result.

## Run a small benchmark

``` shell
cd /benchmark/ && bash run_benchmark_small.sh
```

The command above runs a small benchmark using the following quantum algorithms:
* QFT on `n` qubits, up to 5 qubits
* Grover's algorithm, up to 5 qubits

The command above takes about 5 minutes.

The result will be stored into `/benchmark/result/small`, including the following CSV files:
* `qft.csv`
* `grover.csv`

and a PDF figure file:
* `benchmark.pdf`.

## Run a full benchmark

``` shell
cd /benchmark/ && bash run_benchmark_full.sh
```

The command above runs a full benchmark including the following quantum algorithms:
* Applying Hadamard to the last qubit, up to 40 qubits
* The Deutsch-Jozsa algorithm with the even function as oracle, up to 20 qubits
* Simon's algorithm, with $$s = 2^{n} − 1$$, up to 8 qubits
* Multiple-Control-X with `n` control qubits decomposed to 1- and 2-qubit gates, up to 7 qubits
* QFT on `n` qubits, up to 20 qubits
* Grover's algorithm, up to 7 qubits

The command above takes about **A FEW HOURS**.

The result will be stored into `/benchmark/result/full`, including the following CSV files:
* `had-last-qubit.csv`
* `deutsch-jozsa-is-even-simplified.csv`
* `simon.csv`
* `mcx.csv`
* `qft.csv`
* `grover.csv`

and a PDF figure file:
* `benchmark.pdf`

# Benchmark result format

## Raw data format

The benchmark is organized as *variants*.
Each variant corresponds to an optimization level of [fggs](https://github.com/chihyang/fggs/tree/oopsla_benchmark).
Right now, there are three optimization levels:
* *no_opt*
* *exp_opt*
* *all_opt*

For each variant, there are multiple algorithms.
The following algorithms have been implemented:
* apply Hadamard to the last qubit
* Bell state preparation
* Deutsch-Jozsa, with the constant oracle that always returns 0, where the oracle is simplified to Identity
* Deutsch-Jozsa, with the balanced oracle that checks if a number is even
* Deutsch-Jozsa, with the balanced oracle that checks if a number is even, where the oracle is simplified to CNOT
* Simon's, with the key $$s = 2^{n} - 1$$ for $$n$$ qubits
* Grover
* QFT
* Multiple-Control-Not

For each algorithm of a variant, after the simulation is finished, a CSV file will be generated and put into the specified folder (See [below](#benchmark-cli-command-line-arguments)).
This CSV has the following columns.

| Column name                                 | Meaning                                                                   |
|---------------------------------------------|---------------------------------------------------------------------------|
| `{algorithm}-{variant}:iso-to-perpl`        | The compilation time from ISO to PERPL                                    |
| `{algorithm}-{variant}:perpl-to-fgg`        | The compilation time from PERPL to FGG                                    |
| `{algorithm}-{variant}:iso-simulation`      | The solver run time from the FGG compiled through PERPL                   |
| `{algorithm}-{variant}:iso-to-fgg`          | The compilation time from ISO to FGG                                      |
| `{algorithm}-{variant}:iso-fgg-simulation`  | The solver run time from the FGG compiled from ISO                        |
| `{algorithm}-{variant}:qiskit-simulation`   | The Qiskit simulation time                                                |
| `{algorithm}-{variant}:qsim-simulation`     | The qsim simulation time                                                  |
| `{algorithm}-{variant}:qtorch-simulation`   | The qTorch simulation time                                                |

After all variants are performed, multiple CSV files for one algorithm are merged together.
All columns listed above will be added.
In addition, the following columns will be added.

| Column name                                 | Meaning                                                                   |
|---------------------------------------------|---------------------------------------------------------------------------|
| `{algorithm}-{variant}:iso-perpl-fgg-total` | The simulation plus compilation time from ISO to FGG through PERPL        |
| `{algorithm}-{variant}:iso-fgg-total`       | The simulation plus compilation time from ISO to FGG                      |
| `{algorithm}-avg:iso-to-perpl`              | The average compilation time from ISO to PERPL                            |
| `{algorithm}-avg:perpl-to-fgg`              | The average compilation time from PERPL to FGG                            |
| `{algorithm}-avg:iso-to-fgg`                | The average compilation time from ISO to FGG                              |
| `{algorithm}-avg:iso-perpl-fgg`             | The average compilation time from ISO to FGG through PERPL                |
| `{algorithm}-avg:qiskit-simulation`         | The average Qiskit simulation time of all performed variants              |
| `{algorithm}-avg:qsim-simulation`           | The average qsim simulation time of all performed variants                |
| `{algorithm}-avg:qtorch-simulation`         | The average qTorch simulation time of all performed variants              |
| `{algorithm}-avg:qtorch-simulation-full`    | The average qTorch simulation time multiplied by the number of basis states |

Where `{algorithm}` can be one of the following:

* `had-last-qubit`
* `bell-state`
* `deutsch-jozsa-is-even`
* `deutsch-jozsa-to-zero-simplified`
* `deutsch-jozsa-is-even-simplified`
* `simon`
* `grover`
* `qft`
* `mcx`

and `{variant}` can be one of the following:

* `no_opt`
* `exp_opt`
* `all_opt`

If a metadata table is provided, columns from that table will also be added to the aggregated CSV.
For now, the following metadata for each algorithm is supported:

| Column name    | Meaning              |
|----------------|----------------------|
| `qubit-number` | The number of qubits |
| `gate-number`  | The number of gates  |

## Figures

After aggregating data, the scripts will also generate two series of plots.

In the first series, each subplot compares the simulation performance for one FGG variant, Qiskit, qsim, and qTorch.
If the `--variants` option of the `benchmark_cli.py` is not set through the command line and `all_opt` variant is performed, `all_opt` will be used in this series of plots.
Otherwise, the first performed variant will be put into this series of graphs.
(See the options `--variants` and `--primary_variant` for the benchmark CLI below.)

In the second series, each plot compares the simulation performance of different FGG solver optimizations.
It draws the performance of each FGG optimization variant and the average compilation time from ISO to FGG.

# Docker directory structure

The docker image contains everything you need to run the experiments, in the following structure.

* `/workspace/iso`: the ISO compiler repository
* `/workspace/iso/benchmark/case-generator/cases.rkt`: the Racket benchmark algorithm generator
* `/workspace/perpl`: the PERPL compiler repository
* `/workspace/perpl/fggs`: the FGG solver repository
* `/workspace/iso/benchmark/benchmark-meta-data`: the metadata directory, containing the qubit number and gate number data
* `/workspace/iso/benchmark/benchmark_cli.py`: the benchmark CLI, see below for detailed command line arguments
* `/workspace/iso/benchmark/run_benchmark_small.sh`: the quick script to run a partial benchmark
* `/workspace/iso/benchmark/run_benchmark_full.sh`: the quick script to run a complete benchmark
* `/workspace/iso/benchmark/result_2026_03_14`: the directory holding existing benchmark result data

The following tools are included:

* [Qiskit](https://www.ibm.com/quantum/qiskit) 1.1.1
* [qsim](https://github.com/quantumlib/qsim) 0.22.0
* [qTorch](https://github.com/aspuru-guzik-group/qtorch), commit ID: d564ae6
* [Racket](https://blog.racket-lang.org/2026/02/racket-v9-1.html) 9.1

# Benchmark CLI command line arguments

**NOTE: The following section is for those who need to look into the pipeline. For most users, it can be ignored.**

The core CLI, `/workspace/iso/benchmark/benchmark_cli.py`, supports four modes:

* `run`: run the whole benchmark pipeline, from generating data, running the benchmark, aggregating data, to drawing the figures, which can be regarded as the combination of `generate` + `bench` + `graph`
* `generate`: generate the benchmark data
* `bench`: run one benchmark variant
* `graph`: aggregate data from all benchmark variants and draw figures

The following sections introduce detailed arguments to each mode.
All given examples assume the script is run within the Docker container in the directory `/benchmark/`.

## `run` mode

### Examples

* Run the full benchmark.
``` shell
python /benchmark/benchmark_cli.py run \
       --root /workspace \
       --prefix benchmark_full \
       -o /benchmark/result/full \
       --meta_path /benchmark/benchmark-meta-data/ \
       --experiments had-last-qubit deutsch-jozsa-is-even-simplified simon mcx qft grover
```
* Run a smaller benchmark.

``` shell
python /benchmark/benchmark_cli.py run \
       --root /workspace \
       --prefix benchmark_small \
       --case_limit 5 \
       -o /benchmark/result/small \
       --meta_path /benchmark/benchmark-meta-data/ \
       --experiments grover qft
```

### Usage

``` shell
benchmark_cli.py run [-h] [--root ROOT] [--prefix PREFIX] [--variants VARIANTS [VARIANTS ...]]
    [--primary_variant PRIMARY_VARIANT]
    [--case_limit CASE_LIMIT] [-d] [-t <minutes>] [-m <gigabytes>] [--log LOG_PATH] [-o OUTPUT_PATH]
    [--meta_path METADATA_CSV_PATH]
    [--figure_name FIGURE_NAME] [--experiments EXPERIMENTS [EXPERIMENTS ...]]
    [--exclude_experiments EXCLUDE_EXPERIMENTS [EXCLUDE_EXPERIMENTS ...]]
```

### Options

* `-h`, `--help`: Show this help message and exit.
* `--root {root}`: Workspace root that contains `iso`, `perpl`, and `fggs` repositories (default: `/workspace`).
  All generated benchmark programs will be put into `/{root}/iso`, and the folders are named as `/{root}/iso/{prefix}-{variant}`.
  If `iso`, `perpl`, or `fggs` doesn't exist, report an error and exit.
  If `/{root}/iso/{prefix}-{variant}` already exists and there are existing CSV files in these folders, they will be renamed to `*.csv.old` to avoid interference with the current execution.
* `--prefix {prefix}`: Prefix for generated benchmark directories (default: `benchmark-latest`).
* `--variants {variant} ...`: Optimization variants (default: `['no_opt', 'exp_opt', 'all_opt']`).
* `--primary_variant {primary_variant}`: Variant used by series 1, default to `all_opt` if it is in `--variants`, otherwise default to the first option passed to `--variants`. (default: `None`)
*  `--case_limit {case_limit}`: Limit case count for each algorithm.
   Zero means no limit (default: 0).
*  `-d`, `--dry_run`: Print commands without executing (default: `False`).
*  `-t {minutes}`, `--time_limit {minutes}`: Time limit per algorithm for each qubit number in minutes (default: `5`).
*  `-m {gigabytes}`, `--memory_limit {gigabytes}`: Memory limit per algorithm for each qubit number in GB (default: `95%` of the total memory of the machine).
*  `--log {log_path}`: Base log name (default: `log`).
   Logs for each variant will be named as `{log_path}-{current-time}.log`.
*  `-o {output_path}`, `--output_path {output_path}`: Graph CSV output directory (default: `benchmark_result`).
*  `--meta_path {metadata_csv_path}`: Optional directory with extra metadata CSV files (default: `benchmark-meta-data`).
*  `--figure_name {figure_name}`: Benchmark PDF figure file name.
   The PDF will be put into `--output_path`. (default: `benchmark.pdf`)
*  `--experiments {experiment} ...`: Algorithms to simulate.
   By default, every generated algorithm will be simulated.
*  `--exclude_experiments {exclude_experiment} ...`: Algorithms not to simulate.
   If specified, these algorithms will be excluded from the simulation list.

## `generate` mode

### <a id="generate-example" />Examples

* Generate a directory `/workspace/iso/benchmark-latest-exp_opt` that contains all supported algorithms.

``` shell
python benchmark_cli.py generate --variants exp_opt
```
### Usage

``` shell
benchmark_cli.py generate [-h] [--root ROOT] [--prefix PREFIX] [--variants VARIANTS [VARIANTS ...]] [-d]
```

### Options

* `-h`, `--help`: Show this help message and exit.
* `--root {root}`: Workspace root that contains `iso`, `perpl`, and `fggs` repositories (default: `/workspace`).
  All generated benchmark programs will be put into `/{root}/iso`, and the folders are named as `/{root}/iso/{prefix}-{variant}`.
* `--prefix {prefix}`: Prefix for generated benchmark directories (default: `benchmark-latest`).
* `--variants {variant} ...`: Optimization variants (default: `['no_opt', 'exp_opt', 'all_opt']`).
* `-d`, `--dry_run`: Print commands without executing (default: `False`).

## `bench` mode

###  <a id="bench-example" />Examples

Suppose you have run the command example in [`generate examples`](#generate-example).
You can run the following command to run that benchmark.

``` shell
python benchmark_cli.py bench \
    --benchmark_root /workspace/iso/benchmark-latest-exp_opt \
    --csv_path /workspace/iso/benchmark-latest-exp_opt \
    --case_limit 3 \
    --tag exp_opt \
    --experiments qft
```

After all simulations are performed, a file named as `/workspace/iso/benchmark-latest-exp_opt/qft-exp_opt-{current-date-time}.csv` will be generated.

### Usage

``` shell
benchmark_cli.py bench [-h] --benchmark_root BENCHMARK_ROOT --csv_path CSV_PATH
    [--case_limit CASE_LIMIT] [-d] [-t <minutes>] [-m <gigabytes>]
    [--tag TAG] [--log LOG_PATH] [--experiments EXPERIMENTS [EXPERIMENTS ...]]
    [--exclude_experiments EXCLUDE_EXPERIMENTS [EXCLUDE_EXPERIMENTS ...]]
```

### Options:

* `-h`, `--help`: Show this help message and exit.
* `--benchmark_root {benchmark_root}`: Root directory for one generated benchmark variant (required).
* `--csv_path {csv_path}`: Output directory for benchmark CSV reports (required).
* `--case_limit {case_limit}`: Limit case count for each algorithm.
   Zero means no limit (default: 0).
* `-d`, `--dry_run`: Print commands without executing (default: `False`).
* `-t {minutes}`, `--time_limit {minutes}`: Time limit per command in minutes (default: `5`).
* `-m {gigabytes}`, `--memory_limit {gigabytes}`: Memory limit per command in GB (default: `95%` of the total memory of the machine).
* `--tag {tag}`: Tag used in benchmark CSV headers, which is supposed to be one of `all_opt`, `exp_opt`, and `no_opt`.
  But it is not enforced.
  You can also use different tags from the recommended ones.
* `--log {log_path}`: Base log name (default: log).
   The log will be named as ``{log_path}-{current-time}.log`.
* `--experiments {experiment} ...`: Algorithms to simulate.
   By default, every generated algorithm will be simulated.
* `--exclude_experiments {exclude_experiment} ...`: Algorithms not to simulate.
   If specified, these algorithms will be excluded from the simulation list.

## `graph` mode

### Examples

Suppose you have run the command example in [`generate` examples](#generate-example) and [`bench` examples](#bench-example).
You can run the following command to generate the benchmark result figure.

``` shell
python benchmark_cli.py graph \
    --prefix benchmark-latest \
    --search_root /workspace/iso/ \
    --variants exp_opt \
    --primary_variant exp_opt \
    -o /benchmark/result/example/ \
    --meta_path benchmark-meta-data/ \
    --experiments qft
```

In the folder `/benchmark/result/example`, a CSV file `qft.csv` and a PDF `benchmark.pdf` will be generated.

### Usage

``` shell
benchmark_cli.py graph [-h] --prefix PREFIX
    [-o OUTPUT_PATH] [--meta_path METADATA_CSV_PATH] [--search_root SEARCH_ROOT]
    [--variants VARIANTS [VARIANTS ...]] [--primary_variant PRIMARY_VARIANT]
    [--figure_name FIGURE_NAME]
    [--experiments EXPERIMENTS [EXPERIMENTS ...]]
    [--exclude_experiments EXCLUDE_EXPERIMENTS [EXCLUDE_EXPERIMENTS ...]]
```

### Options

* `-h`, `--help`: Show this help message and exit.
* `--prefix {prefix}`: Prefix for benchmark directories (required).
* `-o {output_path}`, `--output_path {output_path}`: Graph CSV output directory (default: `.`).
* `--meta_path {metadata_csv_path}`: Optional directory with extra metadata CSV files (default: `benchmark-meta-data`).
* `--search_root {search_root}`: Directory whose children are searched (default: `.`).
* `--variants {variant} ...`: Optimization variants (default: `['no_opt', 'exp_opt', 'all_opt']`).
* `--primary_variant {primary_variant}`: Variant used by series 1, default to `all_opt` if it is in `--variants`, otherwise default to the first option passed to `--variants` (default: `None`).
* `--figure_name {figure_name}`: Benchmark PDF output name.
  The PDF will be put into `--output_path`. (default: `benchmark.pdf`).
* `--experiments {experiment} ...`: Algorithm simulation data to aggregate.
   By default, all data under `{search_root}` will be aggregated.
* `--exclude_experiments {exclude_experiment} ...`: Algorithm simulation data not to aggregate.
   If specified, the data of these algorithms will be not be aggregated.
