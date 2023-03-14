from unified_planning.engines import Credits, MetaEngine, Engine
from unified_planning.model import FNode
from unified_planning.plans import ContingentPlan
import unified_planning.engines.mixins as mixins
from unified_planning.engines.mixins.compiler import CompilationKind
import unified_planning as up
from unified_planning.model import ProblemKind
from unified_planning.engines.results import PlanGenerationResultStatus, PlanGenerationResult

from typing import Type, IO, Optional, Callable
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

MetaCredits = Credits('CPOR Meat planner',
                  'BGU',
                  'Guy Shani',
                  'https://github.com/???',
                  'Version 1',
                  'CPOR planner is a lightweight STRIPS planner written in c#.',
                  'we whant to cradit the relevant inner engine as well.'
                )

class CPORImpl(Engine):

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

        assert isinstance(problem, up.model.Problem)

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


class CPORMetaEngineImpl(MetaEngine, mixins.OneshotPlannerMixin):

    def __init__(self, *args, **kwargs):
        MetaEngine.__init__(self, *args, **kwargs)
        mixins.OneshotPlannerMixin.__init__(self)
        self.cnv = UpCporConverter()

    @property
    def name(self) -> str:
        return f"CPORPlanning[{self.engine.name}]"

    @staticmethod
    def is_compatible_engine(engine: Type[Engine]) -> bool:
        return engine.is_oneshot_planner() and engine.supports(ProblemKind({"ACTION_BASED"}))  # type: ignore

    @staticmethod
    def _supported_kind(engine: Type[Engine]) -> "ProblemKind":
        supported_kind = ProblemKind()
        supported_kind.set_problem_class('CONTINGENT')
        supported_kind.set_problem_class("ACTION_BASED")
        supported_kind.set_conditions_kind("NEGATIVE_CONDITIONS")
        supported_kind.set_effects_kind("CONDITIONAL_EFFECTS")
        supported_kind.set_typing('FLAT_TYPING')
        supported_kind.set_typing('HIERARCHICAL_TYPING')
        final_supported_kind = supported_kind.union(engine.supported_kind())
        return final_supported_kind

    @staticmethod
    def _supports(problem_kind: "ProblemKind", engine: Type[Engine]) -> bool:
        return problem_kind <= CPORMetaEngineImpl._supported_kind(engine)

    def SetClassicalPlanner(self, classical):
        self.ClassicalSolver = classical

    @staticmethod
    def get_credits(**kwargs) -> Optional["Credits"]:
        return MetaCredits

    def _solve(self,
        problem: "up.model.AbstractProblem",
        heuristic: Optional[
            Callable[["up.model.state.ROState"], Optional[float]]
        ] = None,
        timeout: Optional[float] = None,
        output_stream: Optional[IO[str]] = None,
    ) -> PlanGenerationResult:

        assert isinstance(problem, up.model.Problem)
        assert isinstance(self.engine, mixins.OneshotPlannerMixin)

        if not self._supports(problem.kind, self.engine):
            return PlanGenerationResult(PlanGenerationResultStatus.UNSOLVABLE_PROVEN, None, self.name)

        self.SetClassicalPlanner(self.engine)

        c_domain = self.cnv.createDomain(problem)
        c_problem = self.cnv.createProblem(problem, c_domain)

        solution = self.cnv.createPlan(c_domain, c_problem)
        actions = self.cnv.createActionTree(solution, problem)

        if solution is None or actions is None:
            return PlanGenerationResult(PlanGenerationResultStatus.UNSOLVABLE_PROVEN, None, self.name)

        return PlanGenerationResult(PlanGenerationResultStatus.SOLVED_SATISFICING, ContingentPlan(actions), self.name)




