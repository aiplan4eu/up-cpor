import os
import sys

# Set environment variables for Python.NET on macOS
# using the Mono runtime installed via Homebrew.
if sys.platform == "darwin":
    os.environ["PYTHONNET_RUNTIME"] = "mono"
    os.environ["PYTHONNET_MONO_LIBMONO"] = "/opt/homebrew/opt/mono/lib/libmonosgen-2.0.dylib"

from pathlib import Path

import pytest
from unified_planning.engines.results import PlanGenerationResultStatus

from cpor_test_utils import (
    TEST_RANDOM_SEED,
    assert_dot_equal,
    parse_dot,
    parse_expected_dot,
    reset_test_seeds,
    solve_cpor_offline,
)
from domains import DOMAINS, TESTS_DIR
from up_test_utils import make_test_environment, parse_test_problem

from up_cpor.converter import UpCporConverter
from CPORLib.Algorithms import CPORPlanner

CPOR_PLANNER_PARAMS = {"random_seed": TEST_RANDOM_SEED}


def _run_cpor_and_write_dot(domain: str, output_path: Path):
    reset_test_seeds(TEST_RANDOM_SEED)
    env = make_test_environment(cpor=True)
    problem = parse_test_problem(domain, env)

    converter = UpCporConverter()
    c_domain = converter.createDomain(problem)
    c_problem = converter.createProblem(problem, c_domain)

    planner = CPORPlanner(c_domain, c_problem)
    solution = planner.OfflinePlanning()
    assert solution is not None, f"CPOR failed to find a solution for {domain}"

    planner.WritePlan(str(output_path), solution)
    return planner, solution


@pytest.mark.parametrize("domain", DOMAINS)
def test_cpor_plan_found(domain: str):
    env = make_test_environment(cpor=True)
    problem = parse_test_problem(domain, env)

    with env.factory.OneshotPlanner(name="CPORPlanning", params=CPOR_PLANNER_PARAMS) as planner:
        result = planner.solve(problem)

    assert result.status == PlanGenerationResultStatus.SOLVED_SATISFICING, (
        f"CPORPlanning failed to find a plan for {domain}: {result.status}"
    )

@pytest.mark.parametrize("domain", DOMAINS)
def test_cpor_matches_expected_plan(domain: str):
    domain_dir = TESTS_DIR / domain
    expected_dot = domain_dir / "out.txt"
    assert expected_dot.exists(), f"Missing expected output: {expected_dot}"

    actual_dot = solve_cpor_offline(domain)["dot_graph"]
    assert_dot_equal(parse_expected_dot(domain), actual_dot, domain)


@pytest.mark.parametrize("domain", DOMAINS)
def test_cpor_generated_plan_is_valid(domain: str):
    assert solve_cpor_offline(domain)["is_valid"], f"CPOR returned an invalid contingent plan for {domain}"


def test_cpor_seeded_doors5_plan_is_reproducible_after_interleaved_solves(tmp_path: Path):
    first_dot = tmp_path / "doors5_first.dot"
    interleaved_dot = tmp_path / "blocks2_interleaved.dot"
    second_dot = tmp_path / "doors5_second.dot"

    _run_cpor_and_write_dot("doors5", first_dot)
    _run_cpor_and_write_dot("blocks2", interleaved_dot)
    _run_cpor_and_write_dot("doors5", second_dot)

    assert_dot_equal(parse_dot(first_dot), parse_dot(second_dot), "doors5[seeded-repeat]")


def test_cpor_seeded_doors5_matches_snapshot_after_prior_seeded_solves(tmp_path: Path):
    for domain in ("blocks2", "blocks3", "blocks7", "colorballs2-2"):
        _run_cpor_and_write_dot(domain, tmp_path / f"{domain}_prelude.dot")

    actual_dot = tmp_path / "doors5_after_seeded_prelude.dot"
    _run_cpor_and_write_dot("doors5", actual_dot)

    assert_dot_equal(parse_dot(TESTS_DIR / "doors5" / "out.txt"), parse_dot(actual_dot), "doors5[seeded-prelude]")
