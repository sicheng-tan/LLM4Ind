import os
import logging
from dotenv import load_dotenv
from langchain_openai import ChatOpenAI

def setup_environment():
    """环境变量和代理配置函数"""
    # 加载.env文件
    load_dotenv()
    
    # 统一加载所有需要的环境变量
    openai_api_key = os.getenv('OPENAI_API_KEY')
    deepseek_api_key = os.getenv('DEEPSEEK_API_KEY')
    qwen_api_key = os.getenv('QWEN_API_KEY')
    gemini_api_key = os.getenv('GEMINI_API_KEY')
    http_proxy = os.getenv('HTTP_PROXY')
    https_proxy = os.getenv('HTTPS_PROXY')
    model_type = os.getenv('MODEL_TYPE', 'gpt-4o')  # 默认为 gpt-4o
    cvc5_binary = os.getenv('CVC5_BINARY', './cvc/cvc5-Linux-x86_64-static/bin/cvc5')  # CVC5二进制文件路径
    cvc4_binary = os.getenv('CVC4_BINARY', './cvc/cvc4_binary/cvc4-1.6-x86_64-linux-opt')  # CVC4二进制文件路径
    vampire_binary = os.getenv('VAMPIRE_BINARY', './vampire/vampire')  # Vampire二进制文件路径
    max_attempts_per_prompt = int(os.getenv('MAX_ATTEMPTS_PER_PROMPT', '3'))  # 每个prompt策略的最大尝试次数
    default_cvc_timeout = int(os.getenv('DEFAULT_CVC_TIMEOUT', '60'))  # 默认CVC5超时时间(初始验证检查)
    # Unused while post-LLM 100s retry is commented out in Mate_new*.py.
    retry_cvc_timeout = int(os.getenv('RETRY_CVC_TIMEOUT', '100'))  # 原实现：加时再证原目标；论文无此步
    combined_cvc_timeout = int(os.getenv('COMBINED_CVC_TIMEOUT', '60'))  # 带引理的CVC5超时时间
    max_recursion_depth = int(os.getenv('MAX_RECURSION_DEPTH', '3'))  # 最大递归深度限制
    task_timeout = int(os.getenv('TASK_TIMEOUT', '1200'))  # 单个任务的超时时间（秒）
    max_parallel_tasks = int(os.getenv('MAX_PARALLEL_TASKS', '20'))  # 最大并行任务数
    solver_routing = os.getenv('SOLVER_ROUTING', 'on')
    solver_routing_decider = os.getenv('SOLVER_ROUTING_DECIDER', 'relative')
    solver_routing_probes = os.getenv('SOLVER_ROUTING_PROBES', 'on')
    solver_routing_llm_min_confidence = float(
        os.getenv('SOLVER_ROUTING_LLM_MIN_CONFIDENCE', '0.55')
    )
    lemma_library = os.getenv('LEMMA_LIBRARY', 'on')
    obligation_tree = os.getenv('OBLIGATION_TREE', 'on')
    feedback_repair_hints = os.getenv('FEEDBACK_REPAIR_HINTS', 'on')
    feedback_progress = os.getenv('FEEDBACK_PROGRESS', 'on')
    prompt_retarget = os.getenv('PROMPT_RETARGET', 'on')
    unproved_not_invalid = os.getenv('UNPROVED_NOT_INVALID', 'on')

    # 代理配置
    if http_proxy and https_proxy:
        os.environ['http_proxy'] = http_proxy
        os.environ['https_proxy'] = https_proxy
        logging.info("代理已启用：%s", http_proxy)
    else:
        logging.info("没有找到代理配置，跳过代理设置。")
    # logging.info("跳过代理设置。")

    # 检查必需的 API 密钥是否存在
    if not openai_api_key:
        raise ValueError("OPENAI_API_KEY is not set in .env file.")
    if model_type == 'deepseek' and not deepseek_api_key:
        raise ValueError("DEEPSEEK_API_KEY is not set in .env file for DeepSeek model.")
    if model_type == 'qwen' and not qwen_api_key:
        raise ValueError("QWEN_API_KEY is not set in .env file for Qwen model.")
    if model_type == 'gemini' and not gemini_api_key:
        raise ValueError("GEMINI_API_KEY is not set in .env file for Gemini model.")
    
    return {
        'OPENAI_API_KEY': openai_api_key,
        'DEEPSEEK_API_KEY': deepseek_api_key,
        'QWEN_API_KEY': qwen_api_key,
        'GEMINI_API_KEY': gemini_api_key,
        'MODEL_TYPE': model_type,
        'CVC5_BINARY': cvc5_binary,
        'CVC4_BINARY': cvc4_binary,
        'VAMPIRE_BINARY': vampire_binary,
        'MAX_ATTEMPTS_PER_PROMPT': max_attempts_per_prompt,
        'DEFAULT_CVC_TIMEOUT': default_cvc_timeout,
        'RETRY_CVC_TIMEOUT': retry_cvc_timeout,
        'COMBINED_CVC_TIMEOUT': combined_cvc_timeout,
        'MAX_RECURSION_DEPTH': max_recursion_depth,
        'TASK_TIMEOUT': task_timeout,
        'MAX_PARALLEL_TASKS': max_parallel_tasks,
        'SOLVER_ROUTING': solver_routing,
        'SOLVER_ROUTING_DECIDER': solver_routing_decider,
        'SOLVER_ROUTING_PROBES': solver_routing_probes,
        'SOLVER_ROUTING_LLM_MIN_CONFIDENCE': solver_routing_llm_min_confidence,
        'LEMMA_LIBRARY': lemma_library,
        'OBLIGATION_TREE': obligation_tree,
        'FEEDBACK_REPAIR_HINTS': feedback_repair_hints,
        'FEEDBACK_PROGRESS': feedback_progress,
        'PROMPT_RETARGET': prompt_retarget,
        'UNPROVED_NOT_INVALID': unproved_not_invalid,
    }

def setup_model(config):
    """根据配置初始化模型"""
    if config['MODEL_TYPE'] == 'deepseek':
        llm = ChatOpenAI(
            model='deepseek-chat',
            openai_api_key=config['DEEPSEEK_API_KEY'],
            openai_api_base='https://api.deepseek.com',
            temperature=0.9,  # 设置 temperature 为 0.9，增加多样性
            top_p=0.9  # 设置 top_p 为 0.9，增加创意
            # max_tokens=1024
        )
        logging.info("使用 DeepSeek-chat 模型进行推理")
    elif config['MODEL_TYPE'] == 'qwen':
        llm = ChatOpenAI(
            model='qwen/qwen3-235b-a22b-2507',
            openai_api_key=config['QWEN_API_KEY'],
            openai_api_base='https://openrouter.ai/api/v1',
            temperature=0.9,  # 设置 temperature 为 0.9，增加多样性
            top_p=0.9  # 设置 top_p 为 0.9，增加创意
        )
        logging.info("使用 Qwen 模型进行推理")
    elif config['MODEL_TYPE'] == 'gemini':
        llm = ChatOpenAI(
            model='google/gemini-2.5-flash',
            openai_api_key=config['GEMINI_API_KEY'],
            openai_api_base='https://openrouter.ai/api/v1',
            temperature=0.9,  # 设置 temperature 为 0.9，增加多样性
            top_p=0.9  # 设置 top_p 为 0.9，增加创意
        )
        logging.info("使用 Gemini 模型进行推理")
    else:
        llm = ChatOpenAI(
            model='openai/gpt-5', # 'openai/gpt-4o-2024-11-20', 
            openai_api_key=config['OPENAI_API_KEY'], 
            openai_api_base='https://openrouter.ai/api/v1',
            temperature=0.9,  # 设置 temperature 为 0.9，增加多样性
            top_p=0.9  # 设置 top_p 为 0.9，增加创意
            # temperature=0.7
        )
        logging.info("使用 GPT-5 模型进行推理.")
    
    return llm