import os
import sys
import clr
import System
if sys.platform.startswith('win'):
    # use the .NET Framework runtime
    System.Environment.SetEnvironmentVariable("COMPLUS_Version", "v4.0.30319")
else:
    # use Mono or .NET Core depending on the platform
    if sys.platform.startswith('linux') or sys.platform.startswith('darwin'):
        System.Environment.SetEnvironmentVariable("MONO_ENV_OPTIONS", "--debug")
    elif sys.platform.startswith('openbsd') or sys.platform.startswith('freebsd'):
        System.Environment.SetEnvironmentVariable("DOTNET_ROOT", "/usr/local/share/dotnet")

PROJECT_PATH = os.path.dirname(os.path.abspath(__file__))
DLL_PATH = os.path.join(PROJECT_PATH, "CPORLib.dll")
clr.AddReference(DLL_PATH)

from CPORLib.PlanningModel import Domain, Problem, ParametrizedAction, PlanningAction, Simulator
from CPORLib.LogicalUtilities import Predicate, ParametrizedPredicate, GroundedPredicate, PredicateFormula, CompoundFormula, Formula
from CPORLib.Algorithms import CPORPlanner, SDRPlanner
from CPORLib.Tools import RandomGenerator, Utilities

from unified_planning.model import FNode, OperatorKind, Fluent, Effect
from unified_planning.model.contingent import SensingAction
from unified_planning.plans import ActionInstance
from unified_planning.plans.contingent_plan import ContingentPlanNode
import unified_planning as up
from unified_planning.shortcuts import Bool

from typing import Dict, Optional, Set


class CporPlanGraphError(RuntimeError):
    pass

class UpCporConverter:
    @staticmethod
    def set_random_seed(seed: int) -> None:
        RandomGenerator.Init(int(seed))

    def createProblem(self, problem, domain):
        p = Problem(problem.name, domain)

        for f, v in problem.initial_values.items():
            if v.is_true():
                gp = self.__CreatePredicate(f, False, None)
                p.AddKnown(gp)

        for c in problem.or_constraints:
            cf = self.__CreateOrFormula(c, [])
            p.AddHidden(cf)

        for c in problem.oneof_constraints:
            cf = self.__CreateOneOfFormula(c, [])
            p.AddHidden(cf)

        goal = CompoundFormula("and")
        for g in problem.goals:
            cp = self.__CreateFormula(g, [])
            goal.AddOperand(cp)
        p.Goal = goal.Simplify()

        return p

    def createCPORPlan(self, c_domain, c_problem):
        solver = CPORPlanner(c_domain, c_problem)
        c_plan = solver.OfflinePlanning()
        return c_plan

    def createSDRPlan(self, c_domain, c_problem):
        solver = SDRPlanner(c_domain, c_problem)
        c_plan = solver.OnlineReplanning()
        return solver, c_plan

    def createSDRSolver(self, c_domain, c_problem):
        solver = SDRPlanner(c_domain, c_problem)
        return solver

    def SDRupdate(self, solver, observation):
        normalized_observation = self.__normalize_sdr_observation(observation)
        applied = solver.SetObservation(normalized_observation)
        return applied

    def __normalize_sdr_observation(self, observation):
        if observation is None or len(observation) == 0:
            return None

        if len(observation) != 1:
            raise ValueError(f"SDR expects at most one grounded observation, got {len(observation)}.")

        fluent_exp, value = next(iter(observation.items()))
        if not isinstance(fluent_exp, FNode) or fluent_exp.node_type != OperatorKind.FLUENT_EXP:
            raise ValueError(f"Unsupported observation key: {fluent_exp!r}")

        if not all(arg.is_object_exp() for arg in fluent_exp.args):
            raise ValueError(f"Observation must be grounded: {fluent_exp}")

        if self.__is_true_observation_value(value):
            return "true"
        if self.__is_false_observation_value(value):
            return "false"

        raise ValueError(f"Unsupported observation value: {value!r}")

    def __is_true_observation_value(self, value) -> bool:
        if isinstance(value, bool):
            return value
        if isinstance(value, FNode):
            return value.is_true()
        return False

    def __is_false_observation_value(self, value) -> bool:
        if isinstance(value, bool):
            return not value
        if isinstance(value, FNode):
            return value.is_false()
        return False

    def SDRGet_action(self, solver, problem)  -> ActionInstance:
        c_action = solver.GetAction()
        return self.__convert_SDR_string_to_action_instance(str(c_action), problem)

    def createSDRSimulator(self, problem):
        c_domain = self.createDomain(problem)
        c_problem = self.createProblem(problem, c_domain)
        c_simulator = Simulator(c_domain, c_problem)
        return c_simulator

    def create_c_problem_and_domain(self, problem):
        return problem.actions,

    def SDRSimulatorApply(self, simulator, problem, action: "up.plans.ActionInstance")-> Dict["up.model.FNode", "up.model.FNode"]:
        str_action = str(action)
        str_action = str_action.replace(',', '').replace(')', '').replace('(', ' ')
        str_obser = simulator.Apply(str_action)
        obser = self.__convert_SDR_string_to_observation(str_obser, problem)
        return obser

    def SDRGoal(self, simulator):
        return simulator.GoalReached


    def createDomain(self, problem):
        d = Domain(problem.name)
        for t in problem.user_types:
            if t.father is None:
                d.AddType(t.name)
            else:
                d.AddType(t.name, t.father.name)

        for o in problem.all_objects:
            d.AddConstant(o.name, o.type.name)

        for f in problem.fluents:
            pp = self.__CreatePredicate(f, True, [])
            d.AddPredicate(pp)

        for a in problem.actions:
            l = []
            pa = ParametrizedAction(a.name)
            for param in a.parameters:
                l.append(param.name)
                pa.AddParameter(param.name, param.type.name)
            if not a.preconditions is None:
                for pre in a.preconditions:
                    formula = self.__CreateFormula(pre, l)
                    pa.Preconditions = formula
            if not a.effects is None and len(a.effects) > 0:
                cp = CompoundFormula("and")
                for eff in a.effects:
                    f_eff = self.__CreateEffectFormula(eff, l)
                    cp.SimpleAddOperand(f_eff)
                if len(cp.Operands) > 0:
                    pa.SetEffects(cp)
            if type(a) is SensingAction:
                if not a.observed_fluents is None:
                    for o in a.observed_fluents:
                        pf = self.__CreateFormula(o, l)
                        pa.Observe = pf

            d.AddAction(pa)
        return d

    def createActionTree(self, solution, problem) -> Optional[ContingentPlanNode]:
        if solution is None:
            return None
        return self.__create_action_tree(solution, problem, {}, set())

    def __create_action_tree(
        self,
        solution,
        problem,
        converted_nodes: Dict[int, ContingentPlanNode],
        active_node_ids: Set[int],
    ) -> Optional[ContingentPlanNode]:
        if solution is None:
            return None

        node_id = self.__get_cpor_node_id(solution)
        if node_id in active_node_ids:
            raise CporPlanGraphError(f"Cycle detected while converting CPOR node {node_id}.")
        cached_node = converted_nodes.get(node_id)
        if cached_node is not None:
            return cached_node

        ai = self.__convert_CPOR_string_to_action_instance(str(solution.Action), problem)
        if ai is None:
            return None

        root = ContingentPlanNode(ai)
        converted_nodes[node_id] = root
        active_node_ids.add(node_id)
        try:
            obser = self.__convert_string_to_observation(str(solution.Action), problem)
            if solution.SingleChild:
                child = self.__create_action_tree(
                    solution.SingleChild, problem, converted_nodes, active_node_ids
                )
                if child is not None:
                    root.add_child({}, child)
            if solution.FalseObservationChild and obser:
                child = self.__create_action_tree(
                    solution.FalseObservationChild, problem, converted_nodes, active_node_ids
                )
                if child is not None:
                    observation = {obser: problem.environment.expression_manager.TRUE()}
                    root.add_child(observation, child)
            if solution.TrueObservationChild and obser:
                child = self.__create_action_tree(
                    solution.TrueObservationChild, problem, converted_nodes, active_node_ids
                )
                if child is not None:
                    observation = {obser: problem.environment.expression_manager.FALSE()}
                    root.add_child(observation, child)
        finally:
            active_node_ids.remove(node_id)
        return root

    def __get_cpor_node_id(self, solution) -> int:
        if hasattr(solution, "ID"):
            return int(solution.ID)
        return id(solution)

    def __CreatePredicate(self, f, bAllParameters, lActionParameters) -> ParametrizedPredicate:
        if type(f) is Fluent:
            if (not bAllParameters) and (lActionParameters is None or len(lActionParameters) == 0):
                pp = GroundedPredicate(f.name)
            else:
                pp = ParametrizedPredicate(f.name)
            for param in f.signature:
                bParam = bAllParameters or (param.name in lActionParameters)
                if bParam:
                    pp.AddParameter(param.name, param.type.name)
                else:
                    pp.AddConstant(param.name, param.type.name)
            return pp
        if type(f) is Effect:
            pp = self.__CreatePredicate(f.fluent, bAllParameters, lActionParameters)
            if self.__is_false_formula_value(f.value):
                pp.Negation = True
            elif not self.__is_true_formula_value(f.value):
                raise ValueError(f"Unsupported effect value: {f.value!r}")
            return pp
        if type(f) is FNode:
            if (not bAllParameters) and (lActionParameters is None or len(lActionParameters) == 0):
                pp = GroundedPredicate(f.fluent().name)
            else:
                pp = ParametrizedPredicate(f.fluent().name)
            for arg in f.args:
                if arg.is_parameter_exp():
                    param = arg.parameter()
                    pp.AddParameter(param.name, param.type.name)
                if arg.is_object_exp():
                    obj = arg.object()
                    pp.AddConstant(obj.name, obj.type.name)
            return pp

    def __CreateEffectFormula(self, effect: Effect, lActionParameters) -> Optional[Formula]:
        if not effect.is_assignment():
            raise NotImplementedError(f"Unsupported effect kind: {effect!r}")
        if effect.is_forall():
            raise NotImplementedError(f"Universal conditional effects are not supported: {effect!r}")

        effect_formula = PredicateFormula(self.__CreatePredicate(effect, False, lActionParameters))
        if not effect.is_conditional():
            return effect_formula

        condition_formula = self.__CreateFormula(effect.condition, lActionParameters)
        if self.__is_true_formula(condition_formula):
            return effect_formula
        if self.__is_false_formula(condition_formula):
            return None

        when_formula = CompoundFormula("when")
        when_formula.AddOperand(condition_formula)
        when_formula.AddOperand(effect_formula)
        return when_formula

    def __CreateFormula(self, n: FNode, lActionParameters) -> Formula:
        if n.node_type == OperatorKind.BOOL_CONSTANT:
            predicate = Utilities.TRUE_PREDICATE if n.is_true() else Utilities.FALSE_PREDICATE
            return PredicateFormula(predicate)
        if n.node_type == OperatorKind.FLUENT_EXP:
            pp = self.__CreatePredicate(n, False, lActionParameters)
            pf = PredicateFormula(pp)
            return pf
        if n.node_type == OperatorKind.AND:
            cp = CompoundFormula("and")
        elif n.node_type == OperatorKind.OR:
            cp = CompoundFormula("or")
        elif n.node_type == OperatorKind.NOT:
            cp = self.__CreateFormula(n.args[0], lActionParameters)
            cp = cp.Negate()
            return cp
        else:
            raise NotImplementedError(f"Unsupported formula node type: {n.node_type}")

        for nSub in n.args:
            fSub = self.__CreateFormula(nSub, lActionParameters)
            cp.SimpleAddOperand(fSub)
        return cp

    def __is_true_formula_value(self, value) -> bool:
        if isinstance(value, bool):
            return value
        if isinstance(value, FNode):
            return value.is_true()
        return False

    def __is_false_formula_value(self, value) -> bool:
        if isinstance(value, bool):
            return not value
        if isinstance(value, FNode):
            return value.is_false()
        return False

    def __is_true_formula(self, formula: Formula) -> bool:
        return isinstance(formula, PredicateFormula) and formula.Predicate == Utilities.TRUE_PREDICATE

    def __is_false_formula(self, formula: Formula) -> bool:
        return isinstance(formula, PredicateFormula) and formula.Predicate == Utilities.FALSE_PREDICATE

    def __CreateOrFormula(self, n, lActionParameters) -> Formula:
        cp = CompoundFormula("or")
        for nSub in n:
            fSub = self.__CreateFormula(nSub, lActionParameters)
            cp.SimpleAddOperand(fSub)
        return cp

    def __CreateOneOfFormula(self, n, lActionParameters) -> Formula:
        cp = CompoundFormula("oneof")
        for nSub in n:
            fSub = self.__CreateFormula(nSub, lActionParameters)
            cp.SimpleAddOperand(fSub)
        return cp

    def __convert_CPOR_string_to_action_instance(self, string, problem) -> 'up.plans.InstantaneousAction':
        if string != 'None':
            assert string[0] == "(" and string[-1] == ")"
            list_str = string[1:-1].replace(":", "").replace('~', ' ').split("\n")
            ac = list_str[0].split(" ")
            action_name = ac[1]
            action_param = ac[2:]
            return self.__convert_string_action_to_action_instance(action_name, action_param, problem)

    def __convert_SDR_string_to_action_instance(self, action_string, problem) -> 'up.plans.InstantaneousAction':
        if action_string != 'None':
            ac = action_string.split()
            action_name = ac[0]
            action_param = ac[1:]
            return self.__convert_string_action_to_action_instance(action_name, action_param, problem)

    def __convert_string_action_to_action_instance(self, action_name, action_param, problem) -> 'up.plans.InstantaneousAction':
        action = problem.action(action_name)
        expr_manager = problem.environment.expression_manager
        param = tuple(expr_manager.ObjectExp(problem.object(o_name)) for o_name in action_param)
        return ActionInstance(action, param)

    def __convert_string_to_observation(self, string, problem):
        if string is not None and string != 'None' and ":observe" in string:
            ob = string.replace("\n", " ").replace(")", "").replace("(", "").split(":observe ")[1]
            obs = ob.split()
            expr_manager = problem.environment.expression_manager
            obse = problem.fluent(obs[0])
            location = tuple(expr_manager.ObjectExp(problem.object(o_name)) for o_name in obs[1:])
            obresv = expr_manager.FluentExp(obse, location)
            return obresv
        return None

    def __convert_SDR_string_to_observation(self, string, problem):
        if string is not None and string != 'None':
            ob = string.replace(")", "").replace("(", "")
            obs = ob.split()
            if obs[0] == "not":
                obs = obs[1:]
                boolean = False
            else:
                boolean = True
            expr_manager = problem.environment.expression_manager
            obse = problem.fluent(obs[0])
            location = tuple(expr_manager.ObjectExp(problem.object(o_name)) for o_name in obs[1:])
            obresv = expr_manager.FluentExp(obse, location)
            return {obresv: Bool(boolean)}
        return None
