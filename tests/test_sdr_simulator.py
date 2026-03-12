import os
import sys

import pytest
from unified_planning.plans import ActionInstance

from domains import DOMAINS, TESTS_DIR
from up_test_utils import make_test_environment, parse_test_problem
from up_cpor.simulator import SDRSimulator
from sdr_test_utils import TEST_RANDOM_SEED, reset_test_seeds, normalize_observation, assert_json_snapshot

# Set environment variables for Python.NET on macOS
# using the Mono runtime installed via Homebrew.
if sys.platform == "darwin":
    os.environ["PYTHONNET_RUNTIME"] = "mono"
    os.environ["PYTHONNET_MONO_LIBMONO"] = "/opt/homebrew/opt/mono/lib/libmonosgen-2.0.dylib"

SCRIPTED_ACTIONS = {
    "blocks2": [
        ("senseclear", ("b1",)),
        ("senseon", ("b2", "b1")),
        ("senseontable", ("b2",)),
    ],
    "blocks3": [
        ("senseclear", ("b3",)),
        ("senseclear", ("b2",)),
        ("senseon", ("b3", "b2")),
    ],
    "blocks7": [
        ("senseon", ("b7", "b4")),
        ("senseon", ("b6", "b1")),
        ("senseclear", ("b5",)),
    ],
    "colorballs2-2": [
        ("observe-ball", ("p1-1", "o1")),
        ("move", ("p1-1", "p1-2")),
        ("observe-ball", ("p1-2", "o2")),
    ],
    "doors5": [
        ("sense-door", ("p1-3", "p1-2")),
        ("sense-door", ("p1-3", "p2-3")),
    ],
    "doors15": [
        ("sense-door", ("p1-8", "p1-7")),
        ("sense-door", ("p1-8", "p2-8")),
    ],
    "localize5": [
        ("checking", ()),
        ("sense-up", ()),
        ("sense-down", ()),
        ("sense-left", ()),
        ("sense-right", ()),
        ("move-right", ()),
        ("checking", ()),
    ],
    "unix1": [
        ("cd-down", ("root", "sub1")),
        ("cd-down", ("sub1", "sub11")),
        ("ls", ("sub11", "my-file")),
    ],
    "wumpus05": [
        ("smell_wumpus", ("p1-1",)),
        ("feel-breeze", ("p1-1",)),
        ("move", ("p1-1", "p1-2")),
        ("feel-breeze", ("p1-2",)),
        ("move", ("p1-2", "p2-2")),
        ("smell_wumpus", ("p2-2",)),
    ],
}

CHECK_GOAL = {
    "blocks2": True,
    "blocks3": True,
    "blocks7": True,
    "colorballs2-2": True,
    "doors5": True,
    "doors15": True,
    "localize5": True,
    "unix1": True,
    "wumpus05": True,
}


def _make_action_instance(problem, action_name: str, obj_names):
    action = problem.action(action_name)
    expr_manager = problem.environment.expression_manager
    params = tuple(expr_manager.ObjectExp(problem.object(name)) for name in obj_names)
    return ActionInstance(action, params)


def _run_scripted_simulator_trace(problem, domain: str):
    reset_test_seeds(TEST_RANDOM_SEED)

    simulator = SDRSimulator(problem, random_seed=TEST_RANDOM_SEED)
    trace = []
    goal_before = None
    goal_after = None

    if CHECK_GOAL[domain]:
        goal_before = simulator.is_goal_reached()
        assert isinstance(goal_before, bool), "SDRSimulator.is_goal_reached() must return bool."

    for action_name, obj_names in SCRIPTED_ACTIONS[domain]:
        action = _make_action_instance(problem, action_name, obj_names)
        observation = simulator.apply(action)
        normalized = normalize_observation(observation)
        assert normalized is None or isinstance(normalized, list), "Observation normalization returned invalid type."
        trace.append({"action": str(action), "observation": normalized})

    if CHECK_GOAL[domain]:
        goal_after = simulator.is_goal_reached()
        assert isinstance(goal_after, bool), "SDRSimulator.is_goal_reached() must return bool."

    return {"goal_before": goal_before, "goal_after": goal_after, "steps": len(trace), "trace": trace}


@pytest.mark.parametrize("domain", DOMAINS)
def test_sdr_simulator_scripted_trace_matches_snapshot(domain: str):
    env = make_test_environment()
    problem = parse_test_problem(domain, env)
    actual = _run_scripted_simulator_trace(problem, domain)
    snapshot_path = TESTS_DIR / domain / "sdr_simulator_scripted.json"
    assert_json_snapshot(actual, snapshot_path, f"{domain}[SDRSimulator-scripted]")


@pytest.mark.parametrize("domain", DOMAINS)
def test_goal_reached_returns_bool(domain: str):
    """GoalReached must check the concrete state, not the belief state.

    A previous bug had Simulator.GoalReached delegate to
    PartiallySpecifiedState.IsGoalState(), which falls through to a SAT
    solver that depends on the Microsoft.Solver.Foundation assembly which is
    only automatically available on Windows. The fix is to move the solver
    DLL at installation time to the package directory.
    """
    reset_test_seeds(TEST_RANDOM_SEED)
    env = make_test_environment()
    problem = parse_test_problem(domain, env)
    simulator = SDRSimulator(problem, random_seed=TEST_RANDOM_SEED)

    result = simulator.is_goal_reached()
    assert isinstance(result, bool), (
        f"is_goal_reached() returned {type(result).__name__}, expected bool"
    )
