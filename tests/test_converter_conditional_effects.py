import os
import re
import sys

# Set environment variables for Python.NET on macOS
# using the Mono runtime installed via Homebrew.
if sys.platform == "darwin":
    os.environ["PYTHONNET_RUNTIME"] = "mono"
    os.environ["PYTHONNET_MONO_LIBMONO"] = "/opt/homebrew/opt/mono/lib/libmonosgen-2.0.dylib"

import unified_planning.environment as up_environment
from unified_planning.engines.results import PlanGenerationResultStatus
from unified_planning.model import Fluent, InstantaneousAction, Object
from unified_planning.model.contingent import SensingAction
from unified_planning.model.contingent.contingent_problem import ContingentProblem

from up_cpor.converter import UpCporConverter
from up_cpor.engine import CPORImpl
from CPORLib.Tools import Options


def _normalize(text: str) -> str:
    text = re.sub(r"\s+", " ", text).strip()
    text = re.sub(r"\(\s+", "(", text)
    text = re.sub(r"\s+\)", ")", text)
    text = re.sub(r"\)\(", ") (", text)
    return text


def _find_action(domain, name: str):
    for action in domain.Actions:
        if action.Name == name:
            return action
    raise AssertionError(f"Missing translated action: {name}")


def _convert_domain(problem):
    return UpCporConverter().createDomain(problem)


def _convert_action(problem, name: str):
    return _find_action(_convert_domain(problem), name)


def _build_boolean_problem(name: str):
    env = up_environment.Environment()
    bool_type = env.type_manager.BoolType()
    problem = ContingentProblem(name, env)
    return env, problem, bool_type


def _build_hidden_flag_problem(name: str):
    env, problem, bool_type = _build_boolean_problem(name)
    expr_manager = env.expression_manager
    flag = Fluent("flag", bool_type, environment=env)
    problem.add_fluent(flag, default_initial_value=False)
    problem.add_oneof_initial_constraint([expr_manager.FluentExp(flag), expr_manager.Not(expr_manager.FluentExp(flag))])
    return env, problem, expr_manager, flag


def _collect_used_predicate_names(domain):
    names = set()
    for action in domain.Actions:
        for formula in (action.Preconditions, action.Effects, action.Observe):
            if formula is None:
                continue
            for predicate in formula.GetAllPredicates():
                names.add(predicate.Name)
    return names


def _plan_has_observation_branch(node) -> bool:
    if node is None:
        return False
    for observation_map, child in node.children:
        if observation_map:
            return True
        if _plan_has_observation_branch(child):
            return True
    return False


def test_converter_preserves_positive_conditional_effects():
    env, problem, bool_type = _build_boolean_problem("conditional_positive")
    expr_manager = env.expression_manager
    flag = Fluent("flag", bool_type, environment=env)
    out = Fluent("out", bool_type, environment=env)
    problem.add_fluent(flag, default_initial_value=False)
    problem.add_fluent(out, default_initial_value=False)

    action = InstantaneousAction("act", _env=env)
    action.add_effect(expr_manager.FluentExp(out), True, expr_manager.FluentExp(flag))
    problem.add_action(action)

    translated = _convert_action(problem, "act")

    assert "(when (flag) (out))" in _normalize(str(translated))


def test_converter_preserves_conditional_delete_effects():
    env, problem, bool_type = _build_boolean_problem("conditional_delete")
    expr_manager = env.expression_manager
    flag = Fluent("flag", bool_type, environment=env)
    out = Fluent("out", bool_type, environment=env)
    problem.add_fluent(flag, default_initial_value=False)
    problem.add_fluent(out, default_initial_value=False)

    action = InstantaneousAction("act", _env=env)
    action.add_effect(expr_manager.FluentExp(out), False, expr_manager.FluentExp(flag))
    problem.add_action(action)

    translated = _convert_action(problem, "act")

    assert "(when (flag) (not (out)))" in _normalize(str(translated))


def test_converter_preserves_mixed_unconditional_and_conditional_effects():
    env, problem, bool_type = _build_boolean_problem("conditional_mixed")
    expr_manager = env.expression_manager
    flag = Fluent("flag", bool_type, environment=env)
    always = Fluent("always", bool_type, environment=env)
    out = Fluent("out", bool_type, environment=env)
    problem.add_fluent(flag, default_initial_value=False)
    problem.add_fluent(always, default_initial_value=False)
    problem.add_fluent(out, default_initial_value=False)

    action = InstantaneousAction("act", _env=env)
    action.add_effect(expr_manager.FluentExp(always), True)
    action.add_effect(expr_manager.FluentExp(out), True, expr_manager.FluentExp(flag))
    problem.add_action(action)

    translated = _convert_action(problem, "act")
    normalized = _normalize(str(translated))

    assert "(always)" in normalized
    assert "(when (flag) (out))" in normalized


def test_converter_preserves_parameterized_conditional_effects():
    env = up_environment.Environment()
    bool_type = env.type_manager.BoolType()
    obj_type = env.type_manager.UserType("obj")
    expr_manager = env.expression_manager
    problem = ContingentProblem("conditional_parameterized", env)
    problem.add_object(Object("o1", obj_type, environment=env))

    marked = Fluent("marked", bool_type, environment=env, item=obj_type)
    done = Fluent("done", bool_type, environment=env, item=obj_type)
    problem.add_fluent(marked, default_initial_value=False)
    problem.add_fluent(done, default_initial_value=False)

    action = InstantaneousAction("act", _env=env, item=obj_type)
    parameter = action.parameter("item")
    action.add_effect(
        expr_manager.FluentExp(done, (expr_manager.ParameterExp(parameter),)),
        True,
        expr_manager.FluentExp(marked, (expr_manager.ParameterExp(parameter),)),
    )
    problem.add_action(action)

    translated = _convert_action(problem, "act")

    assert "(when (marked ?item) (done ?item))" in _normalize(str(translated))


def test_converter_preserves_boolean_conditional_effect_conditions():
    env, problem, bool_type = _build_boolean_problem("conditional_boolean_condition")
    expr_manager = env.expression_manager
    flag = Fluent("flag", bool_type, environment=env)
    other = Fluent("other", bool_type, environment=env)
    third = Fluent("third", bool_type, environment=env)
    out = Fluent("out", bool_type, environment=env)
    problem.add_fluent(flag, default_initial_value=False)
    problem.add_fluent(other, default_initial_value=False)
    problem.add_fluent(third, default_initial_value=False)
    problem.add_fluent(out, default_initial_value=False)

    condition = expr_manager.And(
        expr_manager.FluentExp(flag),
        expr_manager.Or(expr_manager.FluentExp(other), expr_manager.Not(expr_manager.FluentExp(third))),
    )

    action = InstantaneousAction("act", _env=env)
    action.add_effect(expr_manager.FluentExp(out), True, condition)
    problem.add_action(action)

    translated = _convert_action(problem, "act")

    assert "(when (and (flag) (or (other) (not (third)))) (out))" in _normalize(str(translated))


def test_prepare_for_planning_keeps_conditional_effects_consistent():
    env, problem, expr_manager, flag = _build_hidden_flag_problem("conditional_consistency")
    bool_type = env.type_manager.BoolType()
    out = Fluent("out", bool_type, environment=env)
    problem.add_fluent(out, default_initial_value=False)

    action = InstantaneousAction("act", _env=env)
    action.add_effect(expr_manager.FluentExp(out), True, expr_manager.FluentExp(flag))
    action.add_effect(expr_manager.FluentExp(out), False, expr_manager.Not(expr_manager.FluentExp(flag)))
    problem.add_action(action)
    problem.add_goal(expr_manager.FluentExp(out))

    converter = UpCporConverter()
    c_domain = converter.createDomain(problem)
    c_problem = converter.createProblem(problem, c_domain)
    c_problem.PrepareForPlanning()

    translated = _find_action(c_domain, "act")
    assert "P_FALSE" not in _normalize(str(translated))

    _, tagged_domain, _ = c_problem.GetInitialBelief().GetPartiallySpecifiedState().GetTaggedDomainAndProblem(
        Options.DeadendStrategies.Lazy, False
    )
    declared_names = {predicate.Name for predicate in tagged_domain.Predicates}
    used_names = _collect_used_predicate_names(tagged_domain)

    for sentinel in ("P_FALSE", "KP_FALSE", "KNP_FALSE", "KGivenP_FALSE"):
        assert sentinel not in used_names
        assert sentinel not in declared_names


def test_cpor_engine_rejects_hidden_conditional_effects_as_noncontingent_plan():
    env, problem, expr_manager, flag = _build_hidden_flag_problem("conditional_unsat")
    bool_type = env.type_manager.BoolType()
    out = Fluent("out", bool_type, environment=env)
    problem.add_fluent(out, default_initial_value=False)

    action = InstantaneousAction("act", _env=env)
    action.add_effect(expr_manager.FluentExp(out), True, expr_manager.FluentExp(flag))
    problem.add_action(action)
    problem.add_goal(expr_manager.FluentExp(out))

    result = CPORImpl()._solve(problem)

    assert result.status != PlanGenerationResultStatus.SOLVED_SATISFICING
    assert result.plan is None


def test_cpor_engine_returns_branching_plan_for_hidden_conditional_effects():
    env, problem, expr_manager, flag = _build_hidden_flag_problem("conditional_branching")
    bool_type = env.type_manager.BoolType()
    ready_true = Fluent("ready_true", bool_type, environment=env)
    ready_false = Fluent("ready_false", bool_type, environment=env)
    done = Fluent("done", bool_type, environment=env)
    problem.add_fluent(ready_true, default_initial_value=False)
    problem.add_fluent(ready_false, default_initial_value=False)
    problem.add_fluent(done, default_initial_value=False)

    sense = SensingAction("sense_flag", _env=env)
    sense.add_observed_fluent(expr_manager.FluentExp(flag))
    problem.add_action(sense)

    advance = InstantaneousAction("advance", _env=env)
    advance.add_effect(expr_manager.FluentExp(ready_true), True, expr_manager.FluentExp(flag))
    advance.add_effect(expr_manager.FluentExp(ready_false), True, expr_manager.Not(expr_manager.FluentExp(flag)))
    problem.add_action(advance)

    finish_true = InstantaneousAction("finish_true", _env=env)
    finish_true.add_precondition(expr_manager.FluentExp(ready_true))
    finish_true.add_effect(expr_manager.FluentExp(done), True)
    problem.add_action(finish_true)

    finish_false = InstantaneousAction("finish_false", _env=env)
    finish_false.add_precondition(expr_manager.FluentExp(ready_false))
    finish_false.add_effect(expr_manager.FluentExp(done), True)
    problem.add_action(finish_false)

    problem.add_goal(expr_manager.FluentExp(done))

    result = CPORImpl()._solve(problem)

    assert result.status == PlanGenerationResultStatus.SOLVED_SATISFICING
    assert result.plan is not None
    assert _plan_has_observation_branch(result.plan.root_node)
