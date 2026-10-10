#!/usr/bin/bash

# WARNING: this script is intended for running in docker!
python /benchmark/benchmark_cli.py run \
       --root /workspace \
       --prefix benchmark_full \
       -o /benchmark/result/full \
       --meta_path /benchmark/benchmark-meta-data/ \
       --experiments \
       had-last-qubit \
       bell-state \
       casc-had-first-bell \
       casc-had-last-bell \
       para-n-had-last-ten-qubit-bell \
       para-n-had-last-n-bell \
       para-n-ten-qubit-bell \
       para-two-n-bell-state \
       casc-two-n-bell-state \
       deutsch-jozsa-is-even-simplified \
       had-last-dj-even \
       simon \
       mcx \
       qft \
       grover
