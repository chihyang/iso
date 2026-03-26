#!/usr/bin/bash

# WARNING: this script is intended for running in docker!
python /workspace/benchmark/benchmark_cli.py run \
       --root /workspace \
       --prefix benchmark_full \
       -o /benchmark/result/full \
       --meta_path /benchmark/benchmark-meta-data/ \
       --experiments had-last-qubit deutsch-jozsa-is-even-simplified simon mcx qft grover
