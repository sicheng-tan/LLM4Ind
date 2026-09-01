#!/usr/bin/env python3
"""
主程序入口文件
调用 Mate_new.py 中的求解器功能
"""

import argparse
import logging
import sys

import Mate_new as mate_solver

prove_run = mate_solver.prove_run

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="ProofMate 单任务入口")
    parser.add_argument("base_path")
    parser.add_argument("base_name")
    parser.add_argument(
        "--strategy-mode",
        choices=["default", "zero_shot", "naive"],
        default="default",
        help="default/zero_shot: prompts_ours; naive: prompt_naive × 2N",
    )
    parser.add_argument(
        "--baseline",
        action="store_true",
        help="仅求解器初始验证，不调用 LLM",
    )
    args = parser.parse_args()

    final_status = prove_run(
        args.base_path,
        args.base_name,
        strategy_mode=args.strategy_mode,
        baseline_only=args.baseline,
    )

    logging.info("最终验证结论: %s", "成功" if final_status else "Fail")
    logging.info("unsat" if final_status else "")
    sys.exit(0 if final_status else 1)
