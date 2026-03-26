#!/usr/bin/bash

# WARNING: this script is intended for running in docker!
python /benchmark/benchmark_cli.py run \
       --root /workspace \
       --prefix benchmark_small \
       --case_limit 5 \
       -o /benchmark/result/small \
       --meta_path /benchmark/benchmark-meta-data/ \
       --experiments grover qft
