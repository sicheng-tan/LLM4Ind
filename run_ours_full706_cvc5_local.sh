#!/bin/bash
# CVC5 全量 706：DeepSeek-v4-flash + local harvest。
# MAX_PARALLEL_TASKS=20（原 40；ProcessPoolExecutor 读 env，不必改 run_exp_folder.py）。
# LLM_TIMEOUT=180、LLM_MAX_RETRIES=1、HARVEST_RETRY_TIMEOUT=2。
set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

ENV_FILE="$SCRIPT_DIR/experiments/configs/ours_full706_deepseekv4flash_local.env"
if [[ ! -f "$ENV_FILE" ]]; then
    echo "缺少 $ENV_FILE" >&2
    echo "请复制 experiments/configs/ours_full706_deepseekv4flash_local.env.example 并填入密钥。" >&2
    exit 1
fi

export DOTENV_PATH="$ENV_FILE"

RESULT_DIR="$SCRIPT_DIR/experiments/results/ours_full706_deepseekv4flash_cvc5_local"
LOG_DIR="$RESULT_DIR/logs"
mkdir -p "$LOG_DIR"

echo "开始 706 CVC5 local 对照 - $(date)"
echo "DOTENV_PATH=$DOTENV_PATH"
echo "MAX_PARALLEL_TASKS=20  LLM_TIMEOUT=180  LLM_MAX_RETRIES=1  HARVEST_RETRY_TIMEOUT=2"
echo "日志: $LOG_DIR/"

declare -a datasets=("autoproof" "dtt" "ind-ben" "vmcai15-dt")

for dataset in "${datasets[@]}"; do
    path="$SCRIPT_DIR/benchmarks/preprocessed/$dataset"
    TIMESTAMP=$(date +"%Y%m%d_%H%M%S")
    logfile="$LOG_DIR/${TIMESTAMP}_${dataset}.log"

    echo "=========================================="
    echo "正在运行数据集: $dataset"
    echo "日志文件: $logfile"
    echo "开始时间: $(date)"
    echo "=========================================="

    python3 run_exp_folder.py \
        --root-path "$path" \
        --result-dir "$RESULT_DIR" \
        2>&1 | tee "$logfile"
    status=${PIPESTATUS[0]}

    sleep 10
    ./kill_cvc_processes.sh
    sleep 10

    if [ "$status" -eq 0 ]; then
        echo "✓ 数据集 $dataset 执行成功"
        echo "执行成功 - 结束时间: $(date)" >> "$logfile"
    else
        echo "✗ 数据集 $dataset 执行失败"
        echo "执行失败 - 结束时间: $(date)" >> "$logfile"
        echo "错误: 数据集 $dataset 执行失败，请检查日志文件 $logfile"
    fi
    echo ""
done

echo "=========================================="
echo "706 CVC5 local 对照完成 - $(date)"
echo "=========================================="
