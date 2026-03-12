import unified_planning as up
from typing import Dict, Optional
from unified_planning.model.contingent import ExecutionEnvironment

from up_cpor.converter import UpCporConverter

class SDRSimulator(ExecutionEnvironment):

    def __init__(
        self,
        problem: "up.model.contingent.contingent_problem.ContingentProblem",
        random_seed: Optional[int] = None,
    ):
        super().__init__(problem)
        self.problem = problem.clone()
        self.cnv = UpCporConverter()
        if random_seed is not None:
            self.cnv.set_random_seed(random_seed)
        self.simulator = self.cnv.createSDRSimulator(problem)


    def apply(
        self, action: "up.plans.ActionInstance"
    ) -> Dict["up.model.FNode", "up.model.FNode"]:
        return self.cnv.SDRSimulatorApply(self.simulator, self.problem, action)

    def is_goal_reached(self) -> bool:
        return self.cnv.SDRGoal(self.simulator)
