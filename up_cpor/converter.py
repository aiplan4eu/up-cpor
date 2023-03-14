import os
import sys
import clr
import pathlib
PROJECT_PATH = str(pathlib.Path().resolve().parent)
sys.path.remove(PROJECT_PATH)
RELATIVE_DLL_PATH = "CPORLib/obj/Debug/netstandard2.0/CPORLib.dll".replace('/', os.path.sep)
DLL_PATH = os.path.join(PROJECT_PATH, RELATIVE_DLL_PATH)
clr.AddReference(DLL_PATH)

from CPORLib.PlanningModel import Domain, Problem, ParametrizedAction, PlanningAction
from CPORLib.LogicalUtilities import Predicate, ParametrizedPredicate, GroundedPredicate, PredicateFormula, CompoundFormula, Formula
from CPORLib.Algorithms import CPORPlanner
sys.path.append(PROJECT_PATH)

from unified_planning.io import PDDLReader
from unified_planning.model import FNode, OperatorKind, Fluent, Effect, SensingAction
from unified_planning.plans import ActionInstance, ContingentPlanNode
import unified_planning as up


class UpCporConverter:

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

    def createPlan(self, c_domain, c_problem):
        solver = CPORPlanner(c_domain, c_problem)
        # if not self.ClassicalSolver is None:
        #     solver.SetClassicalPlanner(self.ClassicalSolver)
        #     solver.SetParser(PDDLReader())
        c_plan = solver.OfflinePlanning()
        return c_plan


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
                    pp = self.__CreatePredicate(eff, False, l)
                    cp.SimpleAddOperand(pp)
                pa.Effects = cp
            if type(a) is SensingAction:
                if not a.observed_fluents is None:
                    for o in a.observed_fluents:
                        pf = self.__CreateFormula(o, l)
                        pa.Observe = pf

            d.AddAction(pa)
        return d

    def createActionTree(self, solution, problem) -> ContingentPlanNode:
        if solution is not None:
            ai = self.__convert_string_to_action_instance(str(solution.Action), problem)
            if ai:
                root = ContingentPlanNode(ai)
                obser = self.__convert_string_to_observation(str(solution.Action), problem)
                if solution.SingleChild:
                    root.add_child({}, self.createActionTree(solution.SingleChild, problem))
                if solution.FalseObservationChild and obser:
                    observation = {obser: problem.env.expression_manager.TRUE()}
                    root.add_child(observation, self.createActionTree(solution.FalseObservationChild, problem))
                if solution.TrueObservationChild and obser:
                    observation = {obser: problem.env.expression_manager.FALSE()}
                    root.add_child(observation, self.createActionTree(solution.TrueObservationChild, problem))
                return root
        return None

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
            if str(f.value) == "false":
                pp.Negation = True
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

    def __CreateFormula(self, n: FNode, lActionParameters) -> Formula:
        if n.node_type == OperatorKind.FLUENT_EXP:
            pp = self.__CreatePredicate(n, False, lActionParameters)
            pf = PredicateFormula(pp)
            return pf
        else:
            if n.node_type == OperatorKind.AND:
                cp = CompoundFormula("and")
            elif n.node_type == OperatorKind.OR:
                cp = CompoundFormula("or")
            elif n.node_type == OperatorKind.NOT:
                cp = self.__CreateFormula(n.args[0], lActionParameters)
                cp = cp.Negate()
                return cp
            else:
                cp = CompoundFormula("oneof")

            for nSub in n.args:
                fSub = self.__CreateFormula(nSub, lActionParameters)
                cp.SimpleAddOperand(fSub)
            return cp

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



    def __convert_string_to_action_instance(self, string, problem) -> 'up.plans.InstantaneousAction':
        if string != 'None':
            assert string[0] == "(" and string[-1] == ")"
            list_str = string[1:-1].replace(":", "").replace('~', ' ').split("\n")
            ac = list_str[0].split(" ")
            action = problem.action(ac[1])
            expr_manager = problem.env.expression_manager
            param = tuple(expr_manager.ObjectExp(problem.object(o_name)) for o_name in ac[2:])
            return ActionInstance(action, param)

    def __convert_string_to_observation(self, string, problem):
        if string != 'None' and ":observe" in string:
            ob = string.replace("\n", " ").replace(")", "").replace("(", "").split(":observe ")[1]
            obs = ob.split(" ")
            obs = obs[0:2]
            expr_manager = problem.env.expression_manager
            obse = problem.fluent(obs[0])
            location = tuple(expr_manager.ObjectExp(problem.object(o_name)) for o_name in obs[1:])
            obresv = expr_manager.FluentExp(obse, location)
            return obresv
        return None