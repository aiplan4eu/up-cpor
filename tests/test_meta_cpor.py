import os
import sys

# Set environment variables for Python.NET on macOS
# using the Mono runtime installed via Homebrew.
if sys.platform == "darwin":
    os.environ["PYTHONNET_RUNTIME"] = "mono"
    os.environ["PYTHONNET_MONO_LIBMONO"] = "/opt/homebrew/opt/mono/lib/libmonosgen-2.0.dylib"

import pytest
from unified_planning.engines.results import PlanGenerationResultStatus

from cpor_test_utils import TEST_RANDOM_SEED, assert_dot_equal, parse_expected_dot, solve_cpor_offline
from domains import DOMAINS, TESTS_DIR
from up_test_utils import make_test_environment, parse_test_problem

CLASSICAL_PLANNERS = ("tamer", "pyperplan")
META_CPOR_PLANNER_PARAMS = {"random_seed": TEST_RANDOM_SEED}


@pytest.mark.parametrize("classical_planner", CLASSICAL_PLANNERS)
@pytest.mark.parametrize("domain", DOMAINS)
def test_meta_cpor_plan_found(domain: str, classical_planner: str):
    env = make_test_environment(meta_cpor=True)
    problem = parse_test_problem(domain, env)

    with env.factory.OneshotPlanner(
        name=f"MetaCPORPlanning[{classical_planner}]",
        params=META_CPOR_PLANNER_PARAMS,
    ) as planner:
        result = planner.solve(problem)

    assert result.status == PlanGenerationResultStatus.SOLVED_SATISFICING, (
        f"MetaCPOR[{classical_planner}] failed to find a plan for {domain}: {result.status}"
    )


@pytest.mark.parametrize("classical_planner", CLASSICAL_PLANNERS)
@pytest.mark.parametrize("domain", DOMAINS)
def test_meta_cpor_matches_expected_plan(domain: str, classical_planner: str):
    domain_dir = TESTS_DIR / domain
    expected_dot = domain_dir / "out.txt"
    assert expected_dot.exists(), f"Missing expected output: {expected_dot}"

    actual_dot = solve_cpor_offline(domain)["dot_graph"]
    assert_dot_equal(parse_expected_dot(domain), actual_dot, f"{domain}[{classical_planner}]")


@pytest.mark.parametrize("classical_planner", CLASSICAL_PLANNERS)
@pytest.mark.parametrize("domain", DOMAINS)
def test_meta_cpor_generated_plan_is_valid(domain: str, classical_planner: str):
    assert solve_cpor_offline(domain)["is_valid"], (
        f"MetaCPOR[{classical_planner}] returned an invalid contingent plan for {domain}"
    )
