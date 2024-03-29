from unified_planning.io import PDDLReader
import unified_planning.environment as environment
from unified_planning.model.contingent.environment import SimulatedEnvironment
from unified_planning.shortcuts import *


if __name__ == "__main__":

    # Creating a PDDL reader
    reader = PDDLReader()

    prob_arr = ['blocks2', 'doors5', 'wumpus05']

    for prob in prob_arr:
        print(f"###########################Problem: {prob} start###########################")
        # Parsing a PDDL problem from file
        problem = reader.parse_problem(
            f"../Tests/{prob}/d.pddl",
            f"../Tests/{prob}/p.pddl"
        )

        env = environment.get_environment()
        env.factory.add_engine('SDRPlanning', 'up_cpor.engine', 'SDRImpl')

        with ActionSelector(name='SDRPlanning', problem=problem) as solver:
            simulatedEnv = SimulatedEnvironment(problem)
            while not simulatedEnv.is_goal_reached():
                action = solver.get_action()
                observation = simulatedEnv.apply(action)
                solver.update(observation)

