import os
import sys

if sys.platform == "darwin":
    os.environ["PYTHONNET_RUNTIME"] = "mono"
    os.environ["PYTHONNET_MONO_LIBMONO"] = "/opt/homebrew/opt/mono/lib/libmonosgen-2.0.dylib"

import pytest
import unified_planning.environment as up_environment
from unified_planning.model import Fluent, InstantaneousAction
from unified_planning.model.contingent import SensingAction
from unified_planning.model.contingent.contingent_problem import ContingentProblem

from up_cpor.converter import UpCporConverter
from CPORLib.Algorithms import CPORPlanner
from CPORLib.PlanningModel import ConditionalPlanTreeNode
from System import DateTime, NotImplementedException, TimeSpan
from System.Collections.Generic import Dictionary, HashSet


def _build_validation_case():
    env = up_environment.Environment()
    expr_manager = env.expression_manager
    bool_type = env.type_manager.BoolType()

    problem = ContingentProblem("validate_plan_cache_regression", env)
    fluent_a = Fluent("a", bool_type, environment=env)
    fluent_done = Fluent("done", bool_type, environment=env)
    problem.add_fluent(fluent_a, default_initial_value=False)
    problem.add_fluent(fluent_done, default_initial_value=False)
    problem.add_unknown_initial_constraint(expr_manager.FluentExp(fluent_a))
    problem.add_goal(expr_manager.FluentExp(fluent_done))

    finish = InstantaneousAction("finish", _env=env)
    finish.add_effect(expr_manager.FluentExp(fluent_done), True)
    problem.add_action(finish)

    boom = SensingAction("boom", _env=env)
    boom.add_observed_fluent(expr_manager.FluentExp(fluent_a))
    boom.add_effect(expr_manager.FluentExp(fluent_done), True)
    problem.add_action(boom)

    converter = UpCporConverter()
    c_domain = converter.createDomain(problem)
    c_problem = converter.createProblem(problem, c_domain)
    actions = {str(action.Name): action for action in c_domain.Actions}
    initial_state = c_problem.GetInitialBelief().GetPartiallySpecifiedState()
    return initial_state, actions


def _validate(pss, root, cache, active):
    return CPORPlanner.ValidatePlanGraph(
        pss,
        root,
        active,
        cache,
        DateTime.Now,
        TimeSpan(0, 15, 0),
        0,
    )


def test_validate_plan_graph_does_not_cache_exceptional_failures():
    pss, actions = _build_validation_case()

    root = ConditionalPlanTreeNode()
    root.Action = actions["boom"]
    root.TrueObservationChild = ConditionalPlanTreeNode()
    root.FalseObservationChild = ConditionalPlanTreeNode()

    cache = Dictionary[str, bool]()
    active = HashSet[int]()

    with pytest.raises(NotImplementedException):
        _validate(pss, root, cache, active)

    assert active.Count == 0
    assert cache.Count == 0

    with pytest.raises(NotImplementedException):
        _validate(pss, root, cache, active)

    assert active.Count == 0
    assert cache.Count == 0


def test_validate_plan_graph_reuses_successful_root_cache_results():
    pss, actions = _build_validation_case()

    root = ConditionalPlanTreeNode()
    root.Action = actions["finish"]
    root.SingleChild = ConditionalPlanTreeNode()

    cache = Dictionary[str, bool]()
    active = HashSet[int]()

    result, checked_leaves = _validate(pss, root, cache, active)

    assert result
    assert checked_leaves == 1
    assert active.Count == 0
    assert cache.Count > 0

    # Reuse the same node ID with a throwing action. A correct implementation
    # returns the cached success before re-entering the validator body.
    root.Action = actions["boom"]
    root.SingleChild = None
    root.TrueObservationChild = ConditionalPlanTreeNode()
    root.FalseObservationChild = ConditionalPlanTreeNode()

    cached_result, cached_checked_leaves = _validate(pss, root, cache, active)

    assert cached_result
    assert cached_checked_leaves == 0
    assert active.Count == 0
