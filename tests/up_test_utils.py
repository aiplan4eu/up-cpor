import random
from contextlib import contextmanager
from functools import lru_cache

import unified_planning.environment as up_environment
from unified_planning.io import PDDLReader
from unified_planning.model.contingent import SimulatedExecutionEnvironment
from unified_planning.model.contingent.execution_environment import all_smt

from domains import TESTS_DIR


@lru_cache(maxsize=None)
def _make_cached_test_environment(sdr: bool, cpor: bool, meta_cpor: bool):
    env = up_environment.Environment()
    env.credits_stream = None

    if sdr:
        env.factory.add_engine("SDRPlanning", "up_cpor.engine", "SDRImpl")
    if cpor:
        env.factory.add_engine("CPORPlanning", "up_cpor.engine", "CPORImpl")
    if meta_cpor:
        env.factory.add_meta_engine("MetaCPORPlanning", "up_cpor.engine", "CPORMetaEngineImpl")

    env._test_cache_key = (sdr, cpor, meta_cpor)
    return env


def make_test_environment(*, sdr: bool = False, cpor: bool = False, meta_cpor: bool = False):
    return _make_cached_test_environment(sdr, cpor, meta_cpor)


@lru_cache(maxsize=None)
def _parse_cached_test_problem(domain: str, sdr: bool, cpor: bool, meta_cpor: bool):
    env = _make_cached_test_environment(sdr, cpor, meta_cpor)
    reader = PDDLReader(env)
    domain_dir = TESTS_DIR / domain
    return reader.parse_problem(str(domain_dir / "d.pddl"), str(domain_dir / "p.pddl"))


def parse_test_problem(domain: str, env):
    cache_key = getattr(env, "_test_cache_key", None)
    if cache_key is None:
        reader = PDDLReader(env)
        domain_dir = TESTS_DIR / domain
        return reader.parse_problem(str(domain_dir / "d.pddl"), str(domain_dir / "p.pddl"))

    return _parse_cached_test_problem(domain, *cache_key).clone()


class DeterministicSimulatedExecutionEnvironment(SimulatedExecutionEnvironment):
    _MAX_ENUMERATED_MODEL_COUNT = 100_000
    _MIN_SYMBOLS_FOR_SCALABLE_FALLBACK = 100

    def _estimate_model_count_upper_bound(self, problem) -> int:
        count = 1

        for constraint in problem.oneof_constraints:
            count *= len(constraint)
            if count > self._MAX_ENUMERATED_MODEL_COUNT:
                return count

        for constraint in problem.or_constraints:
            count *= (2 ** len(constraint)) - 1
            if count > self._MAX_ENUMERATED_MODEL_COUNT:
                return count

        return count

    def _sample_deterministic_model_without_enumeration(self, formula, symbols):
        from pysmt.shortcuts import Not, Solver

        fixed_assignments = []
        sampled_model = {}

        with Solver(name="z3") as solver:
            solver.add_assertion(formula)

            for symbol in symbols:
                prefer_true = random.choice((True, False))
                preferred_literal = symbol if prefer_true else Not(symbol)
                fallback_literal = Not(symbol) if prefer_true else symbol

                if solver.solve(assumptions=[*fixed_assignments, preferred_literal]):
                    fixed_assignments.append(preferred_literal)
                    sampled_model[symbol] = prefer_true
                else:
                    assert solver.solve(assumptions=[*fixed_assignments, fallback_literal])
                    fixed_assignments.append(fallback_literal)
                    sampled_model[symbol] = not prefer_true

        return sampled_model

    def _randomly_set_full_initial_state(self, problem):
        from pysmt.shortcuts import And, ExactlyOne, Not, Or, Symbol

        fnode_to_symbol = {}
        symbol_to_fnode = {}
        hidden_fluents = [hf for hf in sorted(problem.hidden_fluents, key=str) if not hf.is_not()]

        for cnt, hf in enumerate(hidden_fluents):
            symbol = Symbol(f"v_{cnt}")
            fnode_to_symbol[hf] = symbol
            symbol_to_fnode[symbol] = hf

        constraints = []
        for constraint in problem.oneof_constraints:
            args = []
            for item in sorted(constraint, key=str):
                if item.is_not():
                    args.append(Not(fnode_to_symbol[item.arg(0)]))
                else:
                    args.append(fnode_to_symbol[item])
            constraints.append(ExactlyOne(args))

        for constraint in problem.or_constraints:
            args = []
            for item in sorted(constraint, key=str):
                if item.is_not():
                    args.append(Not(fnode_to_symbol[item.arg(0)]))
                else:
                    args.append(fnode_to_symbol[item])
            constraints.append(Or(args))
            if len(constraints) >= self._max_constraints:
                break

        symbols = sorted(symbol_to_fnode.keys(), key=lambda symbol: symbol.symbol_name())
        formula = And(constraints)

        # Enumerating all satisfying assignments is stable for the existing small
        # regression domains. Only switch to the scalable path for genuinely large
        # uncertainty spaces such as doors15, where the initial uncertainty is
        # roughly 15^7.
        should_enumerate_all_models = (
            len(symbols) < self._MIN_SYMBOLS_FOR_SCALABLE_FALLBACK
            or self._estimate_model_count_upper_bound(problem) <= self._MAX_ENUMERATED_MODEL_COUNT
        )

        if should_enumerate_all_models:
            models = list(all_smt(formula, symbols))
            models.sort(
                key=lambda model: tuple((symbol.symbol_name(), str(model[symbol])) for symbol in symbols)
            )
            sampled_model = random.choice(models)
        else:
            sampled_model = self._sample_deterministic_model_without_enumeration(formula, symbols)

        for symbol in symbols:
            value = sampled_model[symbol]
            if hasattr(value, "is_bool_constant"):
                assert value.is_bool_constant()
                bool_value = value.is_true()
            else:
                bool_value = bool(value)
            self._deterministic_problem.set_initial_value(symbol_to_fnode[symbol], bool_value)


@contextmanager
def use_test_environment(env):
    previous_env = up_environment.GLOBAL_ENVIRONMENT
    up_environment.GLOBAL_ENVIRONMENT = env
    try:
        yield
    finally:
        up_environment.GLOBAL_ENVIRONMENT = previous_env
