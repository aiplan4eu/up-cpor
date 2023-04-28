import unified_planning as up
from typing import Dict
from unified_planning.model.contingent.environment import Environment

from up_cpor.converter import UpCporConverter

class SDRSimulator(Environment):

    def __init__(
        self, problem: "up.model.contingent.contingent_problem.ContingentProblem"
    ):
        super().__init__(problem)
        self.problem = problem.clone()
        self.cnv = UpCporConverter()
        self.simulator = self.cnv.createSDRSimulator(problem)


    def apply(
        self, action: "up.plans.ActionInstance"
    ) -> Dict["up.model.FNode", "up.model.FNode"]:
        return self.cnv.SDRSimulatorApply(self.simulator, self.problem, action)

    def is_goal_reached(self) -> bool:
        return self.cnv.SDRGoal(self.simulator)

