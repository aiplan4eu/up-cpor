import os
import sys
from pathlib import Path

if sys.platform == "darwin":
    os.environ["PYTHONNET_RUNTIME"] = "mono"
    os.environ["PYTHONNET_MONO_LIBMONO"] = "/opt/homebrew/opt/mono/lib/libmonosgen-2.0.dylib"

import unified_planning.environment as up_environment
from unified_planning.model import Fluent, InstantaneousAction
from unified_planning.model.contingent import SensingAction
from unified_planning.model.contingent.contingent_problem import ContingentProblem

from up_cpor.converter import UpCporConverter
from CPORLib.Algorithms import CPORPlanner
from CPORLib.PlanningModel import ConditionalPlanTreeNode


def _finish_branch(finish_action):
    finish = ConditionalPlanTreeNode()
    finish.Action = finish_action
    finish.SingleChild = ConditionalPlanTreeNode()
    return finish


def _make_planner(problem: ContingentProblem):
    converter = UpCporConverter()
    c_domain = converter.createDomain(problem)
    c_problem = converter.createProblem(problem, c_domain)
    planner = CPORPlanner(c_domain, c_problem)
    actions = {str(action.Name): action for action in c_domain.Actions}
    return planner, actions


def _write_plan_text(planner: CPORPlanner, root: ConditionalPlanTreeNode, path: Path) -> str:
    planner.WritePlan(str(path), root)
    return path.read_text()


def _redundant_observation_problem():
    env = up_environment.Environment()
    expr_manager = env.expression_manager
    bool_type = env.type_manager.BoolType()

    problem = ContingentProblem("redundant_observation_writer", env)
    fluent_a = Fluent("a", bool_type, environment=env)
    fluent_done = Fluent("done", bool_type, environment=env)
    problem.add_fluent(fluent_a, default_initial_value=False)
    problem.add_fluent(fluent_done, default_initial_value=False)
    problem.add_unknown_initial_constraint(expr_manager.FluentExp(fluent_a))
    problem.add_goal(expr_manager.FluentExp(fluent_done))

    sense_a = SensingAction("sense_a", _env=env)
    sense_a.add_observed_fluent(expr_manager.FluentExp(fluent_a))
    problem.add_action(sense_a)

    finish = InstantaneousAction("finish", _env=env)
    finish.add_effect(expr_manager.FluentExp(fluent_done), True)
    problem.add_action(finish)

    return problem


def _one_sided_observation_problem():
    env = up_environment.Environment()
    expr_manager = env.expression_manager
    bool_type = env.type_manager.BoolType()

    problem = ContingentProblem("one_sided_observation_writer", env)
    fluent_a = Fluent("a", bool_type, environment=env)
    fluent_b = Fluent("b", bool_type, environment=env)
    fluent_done = Fluent("done", bool_type, environment=env)
    problem.add_fluent(fluent_a, default_initial_value=False)
    problem.add_fluent(fluent_b, default_initial_value=False)
    problem.add_fluent(fluent_done, default_initial_value=False)
    problem.add_unknown_initial_constraint(expr_manager.FluentExp(fluent_a))
    problem.add_unknown_initial_constraint(expr_manager.FluentExp(fluent_b))
    problem.add_unknown_initial_constraint(
        expr_manager.Or(expr_manager.FluentExp(fluent_a), expr_manager.Not(expr_manager.FluentExp(fluent_b)))
    )
    problem.add_goal(expr_manager.FluentExp(fluent_done))

    sense_a = SensingAction("sense_a", _env=env)
    sense_a.add_observed_fluent(expr_manager.FluentExp(fluent_a))
    problem.add_action(sense_a)

    sense_b = SensingAction("sense_b", _env=env)
    sense_b.add_observed_fluent(expr_manager.FluentExp(fluent_b))
    problem.add_action(sense_b)

    finish = InstantaneousAction("finish", _env=env)
    finish.add_effect(expr_manager.FluentExp(fluent_done), True)
    problem.add_action(finish)

    return problem


def test_write_plan_serializes_redundant_observation_subtrees(tmp_path: Path):
    planner, actions = _make_planner(_redundant_observation_problem())

    root = ConditionalPlanTreeNode()
    root.Action = actions["sense_a"]
    root.TrueObservationChild = ConditionalPlanTreeNode()
    root.TrueObservationChild.Action = actions["sense_a"]
    root.FalseObservationChild = ConditionalPlanTreeNode()
    root.FalseObservationChild.Action = actions["sense_a"]

    for child in (root.TrueObservationChild, root.FalseObservationChild):
        child.TrueObservationChild = _finish_branch(actions["finish"])
        child.FalseObservationChild = _finish_branch(actions["finish"])

    assert planner.ValidatePlanGraph(root)

    dot = _write_plan_text(planner, root, tmp_path / "redundant_observation.dot")

    assert dot.count("sense_a") == 3
    assert dot.count("finish") == 4


def test_write_plan_serializes_false_only_observation_subtrees(tmp_path: Path):
    planner, actions = _make_planner(_one_sided_observation_problem())

    root = ConditionalPlanTreeNode()
    root.Action = actions["sense_a"]
    root.TrueObservationChild = ConditionalPlanTreeNode()
    root.TrueObservationChild.Action = actions["sense_b"]
    root.FalseObservationChild = ConditionalPlanTreeNode()
    root.FalseObservationChild.Action = actions["sense_b"]

    for child in (root.TrueObservationChild, root.FalseObservationChild):
        child.TrueObservationChild = _finish_branch(actions["finish"])
        child.FalseObservationChild = _finish_branch(actions["finish"])

    assert planner.ValidatePlanGraph(root)

    dot = _write_plan_text(planner, root, tmp_path / "one_sided_observation.dot")

    assert dot.count("sense_a") == 1
    assert dot.count("sense_b") == 2
    assert dot.count("finish") == 4
