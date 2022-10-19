# Copyright 2021 AIPlan4EU project
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.


from unified_planning.engines import Credits
import unified_planning.engines as engines
from unified_planning.plans import ActionInstance, ContingentPlan
from unified_planning.model import ProblemKind
from unified_planning.engines.results import PlanGenerationResultStatus, PlanGenerationResult
from unified_planning.engines.mixins.compiler import CompilationKind

import os
dirname = os.path.dirname(__file__)
dirname = dirname.split(os.path.sep)[:-1]
dirname = os.path.sep.join(dirname)
filename = os.path.join(dirname, 'CPORLib\\bin\\Debug\\netstandard2.0\\CPORLib.dll')
print(filename)
import clr
clr.AddReference(filename)

from CPORLib.PlanningModel import Domain, Problem, ParametrizedAction, PlanningAction
from CPORLib.LogicalUtilities import Predicate, ParametrizedPredicate, GroundedPredicate, PredicateFormula, CompoundFormula, Formula
from CPORLib.Algorithms import CPORPlanner


credits = Credits('CPOR planner',
                  'BGU',
                  'Guy Shani',
                  'https://github.com/aiplan4eu/up-cpor',
                  'Version 1',
                  'CPOR planner is a lightweight STRIPS planner written in c#.',
                  'CPOR planner is a lightweight STRIPS planner written in c#.\nPlease note that CPOR planner deliberately prefers clean code over fast code. It is designed to be used as a teaching or prototyping tool. If you use it for paper experiments, please state clearly that CPOR planner does not offer state-of-the-art performance.'
                )


class EngineImpl(engines.Engine):
    def __init__(self, bOnline = False, **options):
        self.bOnline = bOnline
        self._skip_checks = False

    @property
    def name(self) -> str:
        return "CPORPlanning"

    @staticmethod
    def supports_compilation(compilation_kind: CompilationKind) -> bool:
        return compilation_kind == CompilationKind.GROUNDING

    @staticmethod
    def supported_kind():
        # Ask what more need to be added
        supported_kind = ProblemKind()
        supported_kind.set_problem_class('CONTINGENT')
        supported_kind.set_problem_class("ACTION_BASED")
        supported_kind.set_typing('FLAT_TYPING')
        supported_kind.set_typing('HIERARCHICAL_TYPING')
        return supported_kind

    @staticmethod
    def supports(problem_kind):
        return problem_kind <= EngineImpl.supported_kind()

    def solve(self, problem: 'up.model.ContingentProblem') -> 'up.engines.results.PlanGenerationResult':

        if not self.supports(problem.kind):
            return PlanGenerationResult(PlanGenerationResultStatus.UNSOLVABLE_PROVEN, None, self.name)

        c_domain = self.__createDomain(problem)
        c_problem = self.__createProblem(problem, c_domain)

        solution = self.__createPlan(c_domain, c_problem)
        actions = self.__createActionTree(solution, problem)
        if solution is None or actions is None:
            return PlanGenerationResult(PlanGenerationResultStatus.UNSOLVABLE_PROVEN, None, self.name)

        return PlanGenerationResult(PlanGenerationResultStatus.SOLVED_SATISFICING, ContingentPlan(actions), self.name)

    def destroy(self):
        pass

    def __createProblem(self, problem, domain):
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

    def __createPlan(self, c_domain, c_problem):
        solver = CPORPlanner(c_domain, c_problem)
        c_plan = solver.OfflinePlanning()
        # handle errors in c# code - null?
        solver.WritePlan("plan.dot", c_plan)
        return c_plan

    def __createDomain(self, problem):
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

    def __createActionTree(self, solution, problem) -> ContingentPlanNode:
        ai = self.__convert_string_to_action_instance(str(solution.Action), problem)
        if ai:
            root = ContingentPlanNode(ai)
            obser = self.__convert_string_to_observation(str(solution.Action), problem)
            if solution.SingleChild:
                root.add_child({}, self.__createActionTree(solution.SingleChild, problem))
            if solution.FalseObservationChild and obser:
                observation = {obser: problem.env.expression_manager.TRUE()}
                root.add_child(observation, self.__createActionTree(solution.FalseObservationChild, problem))
            if solution.TrueObservationChild and obser:
                observation = {obser: problem.env.expression_manager.FALSE()}
                root.add_child(observation, self.__createActionTree(solution.TrueObservationChild, problem))
            return root

    def __convert_string_to_action_instance(self, string, problem) -> 'up.plans.InstantaneousAction':
        if string != 'None':
            assert string[0] == "(" and string[-1] == ")"
            list_str = string[1:-1].replace(":","").replace('~',' ').split("\n")
            ac = list_str[0].split(" ")
            action = problem.action(ac[1])
            expr_manager = problem.env.expression_manager
            param = tuple(expr_manager.ObjectExp(problem.object(o_name)) for o_name in ac[2:])
            return ActionInstance(action, param)

    def __convert_string_to_observation(self, string, problem):
        if string != 'None' and ":observe" in string:
            ob = string.replace("\n"," ").replace(")","").replace("(","").split(":observe ")[1]
            obs = ob.split(" ")
            obs = obs[0:2]
            expr_manager = problem.env.expression_manager
            obse = problem.fluent(obs[0])
            location = tuple(expr_manager.ObjectExp(problem.object(o_name)) for o_name in obs[1:])
            obresv = expr_manager.FluentExp(obse, location)
            return obresv
        return None