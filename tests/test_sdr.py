import os
import sys

import pytest

from domains import DOMAINS, TESTS_DIR
from up_test_utils import (
    DeterministicSimulatedExecutionEnvironment,
    make_test_environment,
    parse_test_problem,
    use_test_environment,
)
from up_cpor.converter import UpCporConverter
from up_cpor.simulator import SDRSimulator
from sdr_test_utils import TEST_RANDOM_SEED, reset_test_seeds, normalize_observation, assert_json_snapshot
from CPORLib.Parsing import Parser

# Set environment variables for Python.NET on macOS
# using the Mono runtime installed via Homebrew.
if sys.platform == "darwin":
    os.environ["PYTHONNET_RUNTIME"] = "mono"
    os.environ["PYTHONNET_MONO_LIBMONO"] = "/opt/homebrew/opt/mono/lib/libmonosgen-2.0.dylib"

SIMULATOR_CONFIG = {
    "blocks2": {"max_steps": 20, "stop_on_goal": True},
    "blocks3": {"max_steps": 4, "stop_on_goal": True},
    "blocks7": {"max_steps": 120, "stop_on_goal": True},
    "colorballs2-2": {"max_steps": 120, "stop_on_goal": True},
    "doors5": {"max_steps": 80, "stop_on_goal": True},
    "doors15": {"max_steps": 500, "stop_on_goal": True},
    "localize5": {"max_steps": 7, "stop_on_goal": False},
    "unix1": {"max_steps": 20, "stop_on_goal": True},
    "wumpus05": {"max_steps": 20, "stop_on_goal": True},
}

SDR_PLANNER_PARAMS = {"random_seed": TEST_RANDOM_SEED}


def _run_online_trace(problem, simulator_cls, max_steps: int, stop_on_goal: bool):
    reset_test_seeds(TEST_RANDOM_SEED)

    all_action_names = {a.name for a in problem.actions}
    trace = []

    with use_test_environment(problem.environment):
        simulator = None
        if simulator_cls is DeterministicSimulatedExecutionEnvironment:
            simulator = simulator_cls(problem)

        with problem.environment.factory.ActionSelector(
            problem=problem,
            name="SDRPlanning",
            params=SDR_PLANNER_PARAMS,
        ) as solver:
            if simulator is None:
                if simulator_cls is SDRSimulator:
                    simulator = simulator_cls(problem, random_seed=TEST_RANDOM_SEED)
                else:
                    simulator = simulator_cls(problem)
            if stop_on_goal:
                while (not simulator.is_goal_reached()) and len(trace) < max_steps:
                    action = solver.get_action()
                    assert action is not None, "SDR returned no action before reaching goal."
                    assert action.action.name in all_action_names, f"Unknown action: {action}"

                    observation = simulator.apply(action)
                    solver.update(observation)
                    trace.append({"action": str(action), "observation": normalize_observation(observation)})

                goal_reached = simulator.is_goal_reached()
                assert goal_reached, f"Goal was not reached within {max_steps} steps."
            else:
                for _ in range(max_steps):
                    action = solver.get_action()
                    if action is None:
                        break
                    assert action.action.name in all_action_names, f"Unknown action: {action}"

                    observation = simulator.apply(action)
                    solver.update(observation)
                    trace.append({"action": str(action), "observation": normalize_observation(observation)})

                goal_reached = None

    return {"goal_reached": goal_reached, "steps": len(trace), "trace": trace}


@pytest.mark.parametrize("domain", DOMAINS)
def test_sdr_online_trace_matches_snapshot_with_up_simulator(domain: str):
    actual = _run_online_trace(
        parse_test_problem(domain, make_test_environment(sdr=True)),
        DeterministicSimulatedExecutionEnvironment,
        **SIMULATOR_CONFIG[domain],
    )
    snapshot_path = TESTS_DIR / domain / "sdr_online_up.json"
    assert_json_snapshot(actual, snapshot_path, f"{domain}[UP]")


@pytest.mark.parametrize("domain", DOMAINS)
def test_sdr_online_trace_matches_snapshot_with_sdr_simulator(domain: str):
    actual = _run_online_trace(
        parse_test_problem(domain, make_test_environment(sdr=True)),
        SDRSimulator,
        **SIMULATOR_CONFIG[domain],
    )
    snapshot_path = TESTS_DIR / domain / "sdr_online_sdrsim.json"
    assert_json_snapshot(actual, snapshot_path, f"{domain}[SDRSimulator]")


def test_sdr_parser_rejects_malformed_grounded_observation():
    env = make_test_environment()
    problem = parse_test_problem("colorballs2-2", env)
    converter = UpCporConverter()
    parser = Parser()
    c_domain = converter.createDomain(problem)

    with pytest.raises(Exception, match=r"Unknown constant o2,"):
        parser.ParseFormula("(not (obj-at o2, p2-2))", c_domain)


def test_sdr_direct_solver_replans_after_false_obj_at_observation():
    reset_test_seeds(TEST_RANDOM_SEED)
    env = make_test_environment()
    problem = parse_test_problem("colorballs2-2", env)
    converter = UpCporConverter()
    c_domain = converter.createDomain(problem)
    c_problem = converter.createProblem(problem, c_domain)
    solver = converter.createSDRSolver(c_domain, c_problem)

    first_action = converter.SDRGet_action(solver, problem)
    assert str(first_action) == "move(p1-1, p2-1)"
    assert converter.SDRupdate(solver, None) is True

    second_action = converter.SDRGet_action(solver, problem)
    assert str(second_action) == "move(p2-1, p2-2)"
    assert converter.SDRupdate(solver, None) is True

    third_action = converter.SDRGet_action(solver, problem)
    assert str(third_action) == "observe-ball(p2-2, o2)"

    expr_manager = problem.environment.expression_manager
    observation = {
        expr_manager.FluentExp(
            problem.fluent("obj-at"),
            (
                expr_manager.ObjectExp(problem.object("o2")),
                expr_manager.ObjectExp(problem.object("p2-2")),
            ),
        ): expr_manager.Bool(False)
    }

    assert converter.SDRupdate(solver, observation) is True

    next_action = converter.SDRGet_action(solver, problem)
    assert next_action is not None
    assert next_action.action.name in {action.name for action in problem.actions}
