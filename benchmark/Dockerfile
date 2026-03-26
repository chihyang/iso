############################
# Stage 1: Builder
############################
FROM python:3.12-slim AS builder

ENV DEBIAN_FRONTEND=noninteractive
ENV BOOTSTRAP_HASKELL_NONINTERACTIVE=1
ENV BOOTSTRAP_HASKELL_GHC_VERSION=9.4.8
ENV BOOTSTRAP_HASKELL_INSTALL_STACK=1

# System deps (build only)
RUN apt update && \
    apt install -y --no-install-recommends \
    curl git ca-certificates build-essential autoconf automake \
    libtool libtool-bin swig libgmp-dev libncurses-dev binutils \
    binutils-gold && \
    rm -rf /var/lib/apt/lists/*

# ----------------------------
# Python venv
# ----------------------------
RUN python -m venv /opt/venv
ENV PATH="/opt/venv/bin:$PATH"

RUN pip install --no-cache-dir --upgrade pip

# Copy requirements first (cache optimization)
COPY requirements.txt /tmp/requirements.txt

RUN pip install --no-cache-dir -r /tmp/requirements.txt

# ----------------------------
# Install Haskell (GHC 9.6.4)
# ----------------------------
RUN curl https://get-ghcup.haskell.org -sSf | sh -s -- -y
ENV PATH="/root/.ghcup/bin:/root/.cabal/bin:/opt/venv/bin:${PATH}"

# ----------------------------
# Install Racket 9.1
# ----------------------------
RUN curl -L -O https://download.racket-lang.org/releases/9.1/installers/racket-9.1-x86_64-linux-buster-cs.sh && \
    chmod +x racket-9.1-x86_64-linux-buster-cs.sh && \
    ./racket-9.1-x86_64-linux-buster-cs.sh --in-place --dest /opt/racket && \
    rm racket-9.1-x86_64-linux-buster-cs.sh

# ----------------------------
# Clone repos
# ----------------------------
WORKDIR /workspace

RUN git clone https://github.com/chihyang/iso.git && \
    git clone https://github.com/chihyang/perpl.git && \
    git clone https://github.com/aspuru-guzik-group/qtorch

# ----------------------------
# Compile qtorch/iso/perpl
# ----------------------------
WORKDIR /workspace/qtorch
RUN sed -i 's/glibtool/libtool/g' Makefile && \
    sed -i 's/sudo //g' Makefile && \
    make install && \
    make all

WORKDIR /workspace/perpl
RUN make

WORKDIR /workspace/iso
RUN git checkout oopsla && \
    stack install --local-bin-path /usr/local/bin

############################
# Stage 2: Runtime
############################
FROM python:3.12-slim

ENV DEBIAN_FRONTEND=noninteractive

# System deps (build only)
RUN apt update && apt install -y --no-install-recommends \
    curl git ca-certificates libgmp10 libncurses6 && \
    rm -rf /var/lib/apt/lists/*

# Copy Python environment
COPY --from=builder /opt/venv /opt/venv

# Copy Racket
COPY --from=builder /opt/racket /opt/racket

WORKDIR /workspace
RUN git clone https://github.com/chihyang/iso.git && \
    git clone https://github.com/chihyang/perpl.git && \
    git clone https://github.com/chihyang/fggs.git && \
    git clone https://github.com/aspuru-guzik-group/qtorch

# Copy qtorch/iso/perpl
COPY --from=builder /workspace/qtorch/bin/ /usr/local/bin/
COPY --from=builder /usr/local/bin/iso-exe /workspace/iso/
COPY --from=builder /workspace/perpl/perplc /workspace/perpl/perplc

# Final PATH
ENV PATH="/opt/venv/bin:/opt/racket/bin:${PATH}"

RUN ln -s /workspace/iso/iso-exe /usr/local/bin/iso-exe && \
    ln -s /workspace/perpl/perplc /usr/local/bin/perplc && \
    mv /workspace/fggs /workspace/perpl/

WORKDIR /workspace/perpl/fggs
RUN git checkout oopsla_benchmark && \
    pip install --no-deps -e .

WORKDIR /workspace/iso
RUN git checkout oopsla

# Copy benchmark
WORKDIR /benchmark
RUN ln -s /workspace/iso/benchmark/benchmark-meta-data /benchmark/benchmark-meta-data && \
    ln -s /workspace/iso/benchmark/benchmark_cli.py /benchmark/benchmark_cli.py && \
    ln -s /workspace/iso/benchmark/run_benchmark_small.sh /benchmark/run_benchmark_small.sh && \
    ln -s /workspace/iso/benchmark/run_benchmark_full.sh /benchmark/run_benchmark_full.sh && \
    ln -s /workspace/iso/benchmark/result_2026_03_14 /benchmark/result_2026_03_14
ENV PATH="/benchmark/:${PATH}"

CMD ["/bin/bash"]
