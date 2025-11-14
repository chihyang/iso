#!/bin/bash

set +x

BENCHMARK_ROOT_DIR="benchmark"
ISO_EXE_PATH="${BENCHMARK_ROOT_DIR}/.."
PERPL_EXE_PATH="${BENCHMARK_ROOT_DIR}/../../perpl"
FGG_EXE_PATH="${BENCHMARK_ROOT_DIR}/../../perpl/fggs"

RUN_QISKIT="false"

function create_dir_if_needed {
    local dir_name="${1}"
    if [ ! -d "${dir_name}" ]; then
        mkdir -p "${dir_name}"
    fi
}

function check_tool {
    local tool_path="${1}"
    if [ ! -f "${tool_path}" ]; then
        echo "$(realpath ${tool_path}) doesn't exist! Make sure the tool exists!"
        exit 1
    fi
}

function check_tools {
    check_tool "${ISO_EXE_PATH}/iso-exe"
    check_tool "${PERPL_EXE_PATH}/perplc"
    check_tool "${FGG_EXE_PATH}/bin/sum_product.py"
}

function run_benchmark {
    local suite_name="${1}"
    local do_python="${2}"
    local iso_suite_dir="${BENCHMARK_ROOT_DIR}/${suite_name}/iso"
    local qiskit_suite_dir="${BENCHMARK_ROOT_DIR}/${suite_name}/python"

    local ppl_dir="${BENCHMARK_ROOT_DIR}/${suite_name}/ppl"
    local json_dir="${BENCHMARK_ROOT_DIR}/${suite_name}/json"
    local iso_result_dir="${BENCHMARK_ROOT_DIR}/${suite_name}/iso-text"
    local qiskit_result_dir="${BENCHMARK_ROOT_DIR}/${suite_name}/qiskit-text"

    create_dir_if_needed "${ppl_dir}"
    create_dir_if_needed "${json_dir}"
    create_dir_if_needed "${iso_result_dir}"
    create_dir_if_needed "${qiskit_result_dir}"

    for file in $(find "${iso_suite_dir}" -type f -name "*.iso" | sort -V); do
        ofile=$(basename ${file} .iso).ppl
        echo "Compiling ${file} to ${ofile}"
        time "${ISO_EXE_PATH}/iso-exe" perpl -o "${ppl_dir}/${ofile}" ${file}
    done

    for file in $(find "${ppl_dir}" -type f -name "*.ppl" | sort -V); do
        ofile=$(basename ${file} .ppl).json
        echo "Compiling ${file} to ${ofile}"
        time "${PERPL_EXE_PATH}/perplc" -s ${file} > "${json_dir}/${ofile}"
    done

    for file in $(find "${json_dir}" -type f -name "*.json" | sort -V); do
        ofile="$(basename ${file} .json)"-iso.txt
        echo "Computing ${file}"
        time python "${FGG_EXE_PATH}/bin/sum_product.py" -d ${file} > "${iso_result_dir}/${ofile}"
        ret=$?
        if [ ${ret} -ne 0 ]; then
            echo "Stop at ${file}, the error code is non-zero (${ret})"
            break
        fi
    done

    if [ "true" == "${do_python}" ]; then
        for file in $(find "${qiskit_suite_dir}" -type f -name "*.py" | sort -V); do
            ofile="$(basename ${file} .py)"-qiskit.txt
            echo "Computing ${file}"
            time python ${file} > "${qiskit_result_dir}/${ofile}"
            ret=$?
            if [ ${ret} -ne 0 ]; then
                echo "Stop at ${file}, the error code is non-zero (${ret})"
                break
            fi
        done
    fi
}

#### Run benchmarks
function print_help {
    cat <<EOF
test.sh [OPTION]...

Options:
  -q, --qiskit: run qiskit test, default false
EOF
}

function parse_args {
    while [[ $# -gt 0 ]]; do
        case $1 in
            -q|--qiskit)
                RUN_QISKIT="true"
                shift # past argument
                ;;
            -h|--help)
                print_help
                exit 0
                ;;
            -*|--*)
                echo "Unknown option $1"
                exit 1
                ;;
            *)
                POSITIONAL_ARGS+=("$1") # save positional arg
                shift # past argument
                ;;
        esac
    done
}

function run_test {
    local do_python="${1}"
    run_benchmark "had-last-qubit" "${do_python}"
    run_benchmark "deutsch-jozsa-to-zero" "${do_python}"
    run_benchmark "deutsch-jozsa-is-even" "${do_python}"
    run_benchmark "simon" "${do_python}"
}

parse_args $@
check_tools
echo "${RUN_QISKIT}"
run_test "${RUN_QISKIT}"
