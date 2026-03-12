import difflib
import json
from pathlib import Path
from typing import Any, Dict, List, Optional

from cpor_test_utils import TEST_RANDOM_SEED, reset_test_seeds


def reset_sdr_seeds(seed: int = TEST_RANDOM_SEED) -> None:
    reset_test_seeds(seed)


def normalize_observation(observation: Optional[Dict[Any, Any]]) -> Optional[List[List[Any]]]:
    if observation is None:
        return None
    if len(observation) == 0:
        return []

    normalized: List[List[Any]] = []
    for fluent, value in observation.items():
        text = str(value).strip().lower()
        if text == "true":
            parsed_value: Any = True
        elif text == "false":
            parsed_value = False
        else:
            parsed_value = str(value)
        normalized.append([str(fluent), parsed_value])

    normalized.sort(key=lambda x: (x[0], str(x[1])))
    return normalized


def assert_json_snapshot(actual: Dict[str, Any], snapshot_path: Path, label: str) -> None:
    expected = json.loads(snapshot_path.read_text(encoding="utf-8"))
    if expected != actual:
        expected_json = json.dumps(expected, indent=2, sort_keys=True)
        actual_json = json.dumps(actual, indent=2, sort_keys=True)
        diff = "\n".join(
            difflib.unified_diff(
                expected_json.splitlines(),
                actual_json.splitlines(),
                fromfile=f"{snapshot_path} (expected)",
                tofile=f"{label} (actual)",
                lineterm="",
            )
        )
        raise AssertionError(f"Snapshot mismatch for {label}\n{diff}")
