import os
import re
import random
from collections import Counter
from functools import lru_cache
from pathlib import Path
from typing import Dict
import tempfile

from pysmt.environment import reset_env as reset_pysmt_env

from domains import TESTS_DIR

_EDGE_RE = re.compile(r"^\s*([A-Za-z0-9_]+)\s*->\s*([A-Za-z0-9_]+)\s*(?:\[[^\]]*\])?\s*;\s*$")
_NODE_RE = re.compile(r"^\s*([A-Za-z0-9_]+)\s*\[(.*)\]\s*;\s*$")
_LABEL_RE = re.compile(r'label\s*=\s*"([^"]*)"')
_BOX_RE = re.compile(r'shape\s*=\s*"box"', re.IGNORECASE)
_ID_PREFIX_RE = re.compile(r"^\s*\d+\)\s*")

TEST_RANDOM_SEED = 0


def reset_test_seeds(seed: int = TEST_RANDOM_SEED) -> None:
    random.seed(seed)
    reset_pysmt_env()

    from up_cpor.converter import UpCporConverter

    UpCporConverter.set_random_seed(seed)


@lru_cache(maxsize=None)
def parse_expected_dot(domain: str) -> Dict[str, object]:
    return parse_dot(TESTS_DIR / domain / "out.txt")


@lru_cache(maxsize=None)
def solve_cpor_offline(domain: str) -> Dict[str, object]:
    from up_cpor.converter import UpCporConverter
    from CPORLib.Algorithms import CPORPlanner
    from up_test_utils import make_test_environment, parse_test_problem

    reset_test_seeds(TEST_RANDOM_SEED)
    problem = parse_test_problem(domain, make_test_environment())

    converter = UpCporConverter()
    c_domain = converter.createDomain(problem)
    c_problem = converter.createProblem(problem, c_domain)

    planner = CPORPlanner(c_domain, c_problem)
    solution = planner.OfflinePlanning()
    assert solution is not None, f"CPOR failed to find a solution for {domain}"

    is_valid = planner.ValidatePlanGraph(solution)

    fd, raw_path = tempfile.mkstemp(suffix=".dot")
    os.close(fd)
    dot_path = Path(raw_path)
    try:
        planner.WritePlan(str(dot_path), solution)
        dot_text = dot_path.read_text(encoding="utf-8")
        dot_graph = parse_dot(dot_path)
    finally:
        dot_path.unlink(missing_ok=True)

    return {
        "dot_text": dot_text,
        "dot_graph": dot_graph,
        "is_valid": is_valid,
    }


def parse_dot(path: Path) -> Dict[str, object]:
    action_nodes: Counter = Counter()
    observation_nodes: Counter = Counter()
    edges: Counter = Counter()

    for raw_line in path.read_text(encoding="utf-8").splitlines():
        line = raw_line.strip()
        if not line or line == "{" or line == "}" or line.startswith("digraph"):
            continue

        edge_match = _EDGE_RE.match(line)
        if edge_match:
            src, dst = edge_match.groups()
            edges[(src, dst)] += 1
            continue

        node_match = _NODE_RE.match(line)
        if not node_match:
            continue

        node_id, attrs = node_match.groups()
        if node_id == "_nil":
            continue

        label_match = _LABEL_RE.search(attrs)
        if label_match is None:
            continue

        label = label_match.group(1)
        if _BOX_RE.search(attrs):
            observation_nodes[(node_id, label.strip().lower() == "true")] += 1
        else:
            normalized = _ID_PREFIX_RE.sub("", label).strip().lower()
            action_nodes[(node_id, normalized)] += 1

    roots = tuple(sorted(dst for (src, dst), count in edges.items() for _ in range(count) if src == "_nil"))
    return {
        "action_nodes": action_nodes,
        "observation_nodes": observation_nodes,
        "edges": edges,
        "roots": roots,
    }


def _format_counter(counter: Counter, limit: int = 12) -> str:
    items = sorted(counter.items())
    trimmed = items[:limit]
    formatted = ", ".join(f"{item} x{count}" for item, count in trimmed)
    if len(items) > limit:
        formatted += f", ... ({len(items) - limit} more)"
    return formatted or "<none>"


def assert_dot_equal(expected: Dict[str, object], actual: Dict[str, object], label: str) -> None:
    messages = []
    for key in ("action_nodes", "observation_nodes", "edges"):
        missing = expected[key] - actual[key]
        extra = actual[key] - expected[key]
        if missing:
            messages.append(f"{key} missing: {_format_counter(missing)}")
        if extra:
            messages.append(f"{key} extra: {_format_counter(extra)}")

    if expected["roots"] != actual["roots"]:
        messages.append(f"roots mismatch: expected={expected['roots']} actual={actual['roots']}")

    assert not messages, f"DOT mismatch for {label}\n" + "\n".join(messages)
