from unified_planning.engines import Credits
from unified_planning.model import FNode
import unified_planning.engines as engines
from unified_planning.plans import ContingentPlan
from unified_planning.engines.mixins.compiler import CompilationKind
import unified_planning as up
from unified_planning.model import ProblemKind
from unified_planning.engines.results import PlanGenerationResultStatus,PlanGenerationResult

from typing import Optional
from up_cpor.converter import UpCporConverter


def print_plan(p_planNode, moves):
    if p_planNode is not None:
        x = p_planNode
        moves.append(x.action_instance)
        for c in x.children:
            moves.append(print_plan(c[1], moves))
    return moves

credits = Credits('CPOR planner',
                  'BGU',
                  'Guy Shani',
                  'https://github.com/???',
                  'Version 1',
                  'CPOR planner is a lightweight STRIPS planner written in c#.',
                  'CPOR planner is a lightweight STRIPS planner written in c#.\nPlease note that CPOR planner deliberately prefers clean code over fast code. It is designed to be used as a teaching or prototyping tool. If you use it for paper experiments, please state clearly that CPOR planner does not offer state-of-the-art performance.'
                )

class CPORImpl(engines.Engine):

    def __init__(self, bOnline = False, **options):
        self.bOnline = bOnline
        self._skip_checks = False
        self.cnv = UpCporConverter()

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
        supported_kind.set_conditions_kind("NEGATIVE_CONDITIONS")
        supported_kind.set_effects_kind("CONDITIONAL_EFFECTS")
        supported_kind.set_typing('FLAT_TYPING')
        supported_kind.set_typing('HIERARCHICAL_TYPING')
        return supported_kind

    @staticmethod
    def supports(problem_kind):
        return problem_kind <= CPORImpl.supported_kind()

    @staticmethod
    def get_credits(**kwargs) -> Optional["Credits"]:
        return credits

    def solve(self, problem: 'up.model.ContingentProblem') -> 'PlanGenerationResult':

        if not self.supports(problem.kind):
            return PlanGenerationResult(PlanGenerationResultStatus.UNSOLVABLE_PROVEN, None, self.name)

        c_domain = self.cnv.createDomain(problem)
        c_problem = self.cnv.createProblem(problem, c_domain)

        solution = self.cnv.createPlan(c_domain, c_problem)
        actions = self.cnv.createActionTree(solution, problem)
        if solution is None or actions is None:
            return PlanGenerationResult(PlanGenerationResultStatus.UNSOLVABLE_PROVEN, None, self.name)

        return PlanGenerationResult(PlanGenerationResultStatus.SOLVED_SATISFICING, ContingentPlan(actions), self.name)

    def destroy(self):
        pass


    def SetClassicalPlanner(self, classical):
        self.ClassicalSolver = classical






