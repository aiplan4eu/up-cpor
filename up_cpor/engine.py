from unified_planning.engines import Credits, MetaEngine, Engine
from unified_planning.model import FNode
from unified_planning.plans import ContingentPlan
import unified_planning.engines.mixins as mixins
from unified_planning.engines.mixins.oneshot_planner import OneshotPlannerMixin
from unified_planning.engines.mixins.action_selector import ActionSelectorMixin
from unified_planning.engines.mixins.compiler import CompilationKind
import unified_planning as up
from unified_planning.model import ProblemKind, AbstractProblem
from unified_planning.model.contingent.contingent_problem import ContingentProblem
from unified_planning.engines.results import PlanGenerationResultStatus, PlanGenerationResult

from typing import Type, IO, Optional, Callable, Dict
from up_cpor.converter import UpCporConverter


MetaCredits = Credits('Conitngent Planning Algorithms',
                    'Guy Shani',
                    'shanigu@bgu.ac.il',
                    'https://github.com/shanigu',
                    '',
                    'Algorithms for offline and online decision making under partial observability and sensing actions',
                    'This package provides a Python API to the algorithms developed by the group of Guy Shani and Ronen Brafman at the Ben Gurion university.\n '
                    'Contingent planning under partial observation and sensing actions models domains where a single agent must make decisions, while some information is unknown, and sensing actions can provide useful information for deciding which actions to execute.\n '
                    'The package contains CPOR, an offline planner that computes complete plan trees, and SDR, an online planner that interleaves planning and execution.'
                      )

CPORCredits = Credits('CPOR',
                    'Guy Shani',
                    'shanigu@bgu.ac.il',
                    'https://github.com/shanigu',
                    '',
                    'CPOR is an offline contingent planner.\n '
                    'It computes a complete plan tree (or graph) where each node is labeled by an action, and edges are labeled by observations.\n'
                    'The leaves of the plan tree correspond to goal states.',
                    'CPOR uses the SDR translation to compute actions.\n '
                    'When a sensing action is chosen, CPOR expands both child nodes corresponding to the possible observations.\n'
                    'CPOR contains a mechanism for reusing plan segments, resulting in a more compact graph.\n	'
                    'Complete information can be found at the followign paper: Computing Contingent Plan Graphs using Online Planning, Maliah and Shani,TAAS,2021.'
)

SDRCredits = Credits('SDR',
                    'Guy Shani',
                    'shanigu@bgu.ac.il',
                    'https://github.com/shanigu',
                    '',
                    'SDR is an online contingent replanner.\n'
                    'It provides one action at a time, and then awaits to receive an observation from the environment.',
                    'SDR operates by compiling a contingent problem into a classical problem, representing only some of the partial knowledge that the agent has. \n	'
                    'The classical problem is then solved. If an action is not applicable, due to the partial information, SDR modifies the classical problem and replans. \n	'
                    'Complete information can be found at the followign paper: Replanning in Domains with Partial Information and Sensing Actions, Brafman and Shani, JAIR, 2012.'
                )

class CPORImpl(Engine, OneshotPlannerMixin):

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
        return CPORCredits

    def solve(self, problem: AbstractProblem) -> 'PlanGenerationResult':

        assert isinstance(problem, ContingentProblem)

        if not self.supports(problem.kind):
            return PlanGenerationResult(PlanGenerationResultStatus.UNSOLVABLE_PROVEN, None, self.name)

        c_domain = self.cnv.createDomain(problem)
        c_problem = self.cnv.createProblem(problem, c_domain)

        solution = self.cnv.createCPORPlan(c_domain, c_problem)
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
    def _supported_kind(engine: Type[Engine]) -> ProblemKind:
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
    def _supports(problem_kind: ProblemKind, engine: Type[Engine]) -> bool:
        return problem_kind <= CPORMetaEngineImpl._supported_kind(engine)

    def SetClassicalPlanner(self, classical):
        self.ClassicalSolver = classical

    @staticmethod
    def get_credits(**kwargs) -> Optional["Credits"]:
        return MetaCredits

    def _solve(self,
        problem: AbstractProblem,
        heuristic: Optional[
            Callable[["up.model.state.State"], Optional[float]]
        ] = None,
        timeout: Optional[float] = None,
        output_stream: Optional[IO[str]] = None,
    ) -> PlanGenerationResult:

        assert isinstance(problem, ContingentProblem)
        assert isinstance(self.engine, mixins.OneshotPlannerMixin)

        if not self._supports(problem.kind, self.engine):
            return PlanGenerationResult(PlanGenerationResultStatus.UNSOLVABLE_PROVEN, None, self.name)

        self.SetClassicalPlanner(self.engine)

        c_domain = self.cnv.createDomain(problem)
        c_problem = self.cnv.createProblem(problem, c_domain)

        solution = self.cnv.createCPORPlan(c_domain, c_problem)
        actions = self.cnv.createActionTree(solution, problem)

        if solution is None or actions is None:
            return PlanGenerationResult(PlanGenerationResultStatus.UNSOLVABLE_PROVEN, None, self.name)

        return PlanGenerationResult(PlanGenerationResultStatus.SOLVED_SATISFICING, ContingentPlan(actions), self.name)


class SDRImpl(Engine, ActionSelectorMixin):

    def __init__(self, bOnline = False, problem: AbstractProblem = None, **options):
        self._skip_checks = False
        self.cnv = UpCporConverter()
        self.problem = problem
        self.solver = self._setSolver(self.problem)
        self.bOnline = bOnline

    @property
    def name(self) -> str:
        return "SDRPlanning"

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
        return problem_kind <= SDRImpl.supported_kind()

    @staticmethod
    def get_credits(**kwargs) -> Optional["Credits"]:
        return SDRCredits

    def solve(self, problem: AbstractProblem) -> 'PlanGenerationResult':

        assert isinstance(problem, ContingentProblem)

        if not self.supports(problem.kind):
            return PlanGenerationResult(PlanGenerationResultStatus.UNSOLVABLE_PROVEN, None, self.name)

        c_domain = self.cnv.createDomain(problem)
        c_problem = self.cnv.createProblem(problem, c_domain)
        self.solver, solution = self.cnv.createSDRPlan(c_domain, c_problem)

        if not self.bOnline:
            actions = self.cnv.createActionTree(solution, problem)
            if solution is None or actions is None:
                return PlanGenerationResult(PlanGenerationResultStatus.UNSOLVABLE_PROVEN, None, self.name)

            return PlanGenerationResult(PlanGenerationResultStatus.SOLVED_SATISFICING, ContingentPlan(actions), self.name)

        else:
            PlanGenerationResult(PlanGenerationResultStatus.INTERMEDIATE, None, self.name)

    def destroy(self):
        pass

    def _get_action(self) -> "up.plans.ActionInstance":
        return self.cnv.SDRget_action(self.solver, self.problem)

    def _update(self, observation: Dict["up.model.FNode", "up.model.FNode"]):
        return self.cnv.SDRupdate(self.solver, observation)

    def _setSolver(self, problem):
        c_domain = self.cnv.createDomain(problem)
        c_problem = self.cnv.createProblem(problem, c_domain)
        solver = self.cnv.createSDRSolver(c_domain, c_problem)
        return solver



