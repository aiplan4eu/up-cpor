import os
import sys

# Set environment variables for Python.NET on macOS
# using the Mono runtime installed via Homebrew.
if sys.platform == "darwin":
    os.environ["PYTHONNET_RUNTIME"] = "mono"
    os.environ["PYTHONNET_MONO_LIBMONO"] = "/opt/homebrew/opt/mono/lib/libmonosgen-2.0.dylib"

import up_cpor.converter  # noqa: F401 – loads CPORLib.dll and ensures Z3 native lib

from CPORLib.PlanningModel import Domain, Problem
from CPORLib.LogicalUtilities import (
    CompoundFormula,
    GroundedPredicate,
    PredicateFormula,
    Formula,
)
from System.Collections.Generic import List as CsList


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _gp(name):
    """Create a GroundedPredicate with the given name."""
    return GroundedPredicate(name)


def _oneof(*preds):
    """Create a oneof CompoundFormula over the given predicates."""
    cf = CompoundFormula("oneof")
    for p in preds:
        cf.SimpleAddOperand(PredicateFormula(p))
    return cf


def _and(*preds):
    """Create an 'and' CompoundFormula over the given predicates."""
    cf = CompoundFormula("and")
    for p in preds:
        cf.SimpleAddOperand(PredicateFormula(p))
    return cf


def _or(*preds):
    """Create an 'or' CompoundFormula over the given predicates."""
    cf = CompoundFormula("or")
    for p in preds:
        cf.SimpleAddOperand(PredicateFormula(p))
    return cf


def _and_cf(*formulas):
    """Create an 'and' CompoundFormula over sub-formulas (not bare predicates)."""
    cf = CompoundFormula("and")
    for f in formulas:
        cf.AddOperand(f)
    return cf


def _make_bs(hidden_cfs):
    """Build a BeliefState with the given hidden CompoundFormulas."""
    domain = Domain("test")
    prob = Problem("test", domain)
    for cf in hidden_cfs:
        prob.AddHidden(cf)
    return prob.GetInitialBelief()


def _hidden_formulas(bs):
    """Return a CsList[Formula] copied from bs.Hidden (skip nulls)."""
    lf = CsList[Formula]()
    for f in bs.Hidden:
        if f is not None:
            lf.Add(f)
    return lf


# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------

def test_z3_sat_returns_valid_assignment():
    """Z3 SAT branch: solver finds a valid assignment."""
    p1, p2, p3 = _gp("p1"), _gp("p2"), _gp("p3")
    bs = _make_bs([_oneof(p1, p2), _oneof(p1, p3)])

    formulas = _hidden_formulas(bs)
    result = bs.RunSatSolver(formulas, 1)

    assert result.Count > 0, "Expected SAT but got empty assignment list"
    # No predicate should appear both positive and negated
    assignment = result[0]
    names_pos = {p.Name for p in assignment if not p.Negation}
    names_neg = {p.Name for p in assignment if p.Negation}
    both = names_pos & names_neg
    assert not both, f"Predicates appear both positive and negated: {both}"


def test_z3_unsat_returns_empty():
    """Z3 UNSAT branch: contradictory constraints yield empty list."""
    p1, p2, p3 = _gp("p1"), _gp("p2"), _gp("p3")
    # Three pairwise oneof constraints over 3 variables are unsatisfiable:
    # each pair must have exactly one true, but 3 variables can't satisfy that.
    bs = _make_bs([_oneof(p1, p2)])

    formulas = _hidden_formulas(bs)
    formulas.Add(_oneof(p2, p3))
    formulas.Add(_oneof(p3, p1))

    result = bs.RunSatSolver(formulas, 1)
    assert result.Count == 0, "Expected UNSAT but got assignments"


def test_unit_prop_contradiction_returns_empty():
    """Unit propagation detects a contradiction and returns empty."""
    p1, p2 = _gp("p1"), _gp("p2")
    bs = _make_bs([_oneof(p1, p2), _oneof(p1.Negate(), p2)])

    formulas = _hidden_formulas(bs)
    formulas.Add(PredicateFormula(p1))  # seed for unit propagation

    result = bs.RunSatSolver(formulas, 1)
    assert result.Count == 0, "Expected unit-prop contradiction but got assignments"


def test_unit_prop_solves_all():
    """Unit propagation resolves everything (no Z3 needed)."""
    p1, p2 = _gp("p1"), _gp("p2")
    bs = _make_bs([_oneof(p1, p2)])

    formulas = _hidden_formulas(bs)
    formulas.Add(PredicateFormula(p1))  # seed

    result = bs.RunSatSolver(formulas, 1)
    assert result.Count > 0, "Expected unit-prop solution but got empty list"


def test_consistent_with_compound_sat():
    """ConsistentWith → RunSatSolver → SAT path."""
    p1, p2 = _gp("p1"), _gp("p2")
    bs = _make_bs([_oneof(p1, p2)])

    query = _or(p1, p2)
    assert bs.ConsistentWith(query, False) is True, (
        "Expected ConsistentWith to return True (SAT)"
    )


def test_consistent_with_compound_unsat():
    """ConsistentWith → RunSatSolver → UNSAT → AddReasoningFormula path."""
    p1, p2, p3 = _gp("p1"), _gp("p2"), _gp("p3")
    bs = _make_bs([_oneof(p1, p2), _oneof(p1, p3)])

    # oneof(p2,p3) in CNF: and(or(p2,p3), or(NOT_p2,NOT_p3))
    # ToCNF() does not support oneof, so express it as the equivalent CNF.
    query = _and_cf(_or(p2, p3), _or(p2.Negate(), p3.Negate()))
    assert bs.ConsistentWith(query, False) is False, (
        "Expected ConsistentWith to return False (UNSAT)"
    )
