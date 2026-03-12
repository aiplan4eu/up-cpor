import os
import sys

# Set environment variables for Python.NET on macOS
# using the Mono runtime installed via Homebrew.
if sys.platform == "darwin":
    os.environ["PYTHONNET_RUNTIME"] = "mono"
    os.environ["PYTHONNET_MONO_LIBMONO"] = "/opt/homebrew/opt/mono/lib/libmonosgen-2.0.dylib"

import unified_planning.environment as up_environment
from unified_planning.model import Fluent
from unified_planning.model.contingent import SensingAction
from unified_planning.model.contingent.contingent_problem import ContingentProblem

from up_cpor.converter import UpCporConverter
from System.Collections.Generic import Dictionary, HashSet, List
from System.Reflection import BindingFlags
from CPORLib.LogicalUtilities import GroundedPredicate, Predicate
from CPORLib.PlanningModel import ConditionalPlanTreeNode, PartiallySpecifiedState
from CPORLib.Tools import GenericArraySet


def _build_closed_state_case(
    required_observation: tuple[str, str] | None,
    *,
    matching_belief: bool = True,
    extra_current_observation: str | None = None,
    known_dependencies: tuple[str, ...] = (),
):
    env = up_environment.Environment()
    expr_manager = env.expression_manager
    bool_type = env.type_manager.BoolType()

    problem = ContingentProblem("closed_state_regression", env)
    fluent_a = Fluent("a", bool_type, environment=env)
    fluent_b = Fluent("b", bool_type, environment=env)
    problem.add_fluent(fluent_a, default_initial_value=False)
    problem.add_fluent(fluent_b, default_initial_value=False)
    problem.add_unknown_initial_constraint(expr_manager.FluentExp(fluent_a))
    problem.add_unknown_initial_constraint(expr_manager.FluentExp(fluent_b))

    sense_a = SensingAction("sense_a", _env=env)
    sense_a.add_observed_fluent(expr_manager.FluentExp(fluent_a))
    problem.add_action(sense_a)

    sense_b = SensingAction("sense_b", _env=env)
    sense_b.add_observed_fluent(expr_manager.FluentExp(fluent_b))
    problem.add_action(sense_b)

    converter = UpCporConverter()
    c_domain = converter.createDomain(problem)
    field = c_domain.GetType().GetField(
        "<IsSimple>k__BackingField",
        BindingFlags.Instance | BindingFlags.NonPublic,
    )
    field.SetValue(c_domain, True)
    c_problem = converter.createProblem(problem, c_domain)

    initial_state = c_problem.GetInitialBelief().GetPartiallySpecifiedState()
    _, _, current_state, _ = initial_state.ApplyOffline("sense_a")
    closed_state = current_state.Clone() if matching_belief else initial_state.Clone()

    actions = {str(action.Name): action for action in c_domain.Actions}
    observed_a = list(actions["sense_a"].Observe.GetAllPredicates())[0]
    observed_b = list(actions["sense_b"].Observe.GetAllPredicates())[0]

    closed_state.m_lOfflinePredicatesKnown = GenericArraySet[Predicate]()
    closed_state.m_lOfflinePredicatesUnknown = GenericArraySet[Predicate]()
    for dependency in known_dependencies:
        closed_state.m_lOfflinePredicatesKnown.Add(observed_a if dependency == "a" else observed_b)

    if extra_current_observation == "b":
        _, _, current_state, _ = current_state.ApplyOffline("sense_b")

    if required_observation is not None:
        reasoned_name, required_name = required_observation
        reasoned_predicate = observed_a if reasoned_name == "a" else observed_b
        required_predicate = observed_a if required_name == "a" else observed_b
        required_observations = Dictionary[GroundedPredicate, List[HashSet[GroundedPredicate]]]()
        required_set = HashSet[GroundedPredicate]()
        required_set.Add(required_predicate)
        required_list = List[HashSet[GroundedPredicate]]()
        required_list.Add(required_set)
        required_observations[reasoned_predicate] = required_list
        closed_state.m_dRequiredObservationsForReasoning = required_observations

    sentinel_plan = ConditionalPlanTreeNode()
    closed_state.Plan = sentinel_plan

    closed_states = List[PartiallySpecifiedState]()
    closed_states.Add(closed_state)
    return current_state, closed_states, sentinel_plan


def test_is_closed_state_reuses_simple_closed_state_without_required_observations():
    current_state, closed_states, sentinel_plan = _build_closed_state_case(required_observation=None)

    assert current_state.IsClosedState(closed_states)
    assert current_state.Plan.ID == sentinel_plan.ID


def test_is_closed_state_reuses_simple_closed_state_with_consistent_required_observations():
    current_state, closed_states, sentinel_plan = _build_closed_state_case(required_observation=("a", "a"))

    assert current_state.IsClosedState(closed_states)
    assert current_state.Plan.ID == sentinel_plan.ID


def test_is_closed_state_rejects_inconsistent_required_observations_when_unknowns_are_empty():
    current_state, closed_states, _ = _build_closed_state_case(required_observation=("b", "a"))

    assert not current_state.IsClosedState(closed_states)


def test_is_closed_state_rejects_non_identical_belief_snapshots():
    current_state, closed_states, _ = _build_closed_state_case(
        required_observation=None,
        matching_belief=False,
    )

    assert not current_state.IsClosedState(closed_states)


def test_is_closed_state_reuses_when_extra_observations_are_irrelevant_to_dependencies():
    current_state, closed_states, sentinel_plan = _build_closed_state_case(
        required_observation=None,
        extra_current_observation="b",
        known_dependencies=("a",),
    )

    assert current_state.IsClosedState(closed_states)
    assert current_state.Plan.ID == sentinel_plan.ID
