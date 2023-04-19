from unified_planning.io import PDDLReader
import unified_planning.environment as environment
from unified_planning.shortcuts import *

from up_cpor.engine import CPORImpl

if __name__ == "__main__":

    # Creating a PDDL reader
    reader = PDDLReader()

    prob_arr = ['blocks2', 'blocks3', 'doors5', 'wumpus05', ]
    prob_fails_arr = ['blocks7', 'medpks010', 'colorballs2-2', 'unix1', 'wumpus10']
    large_prob_arr = ['doors15', ]
    no_sol_pro = ['localize5', ]

    for prob in prob_arr:
        print(f"###########################Problem: {prob} start###########################")
        # Parsing a PDDL problem from file
        problem = reader.parse_problem(
            f"../Tests/{prob}/d.pddl",
            f"../Tests/{prob}/p.pddl"
        )

        env = environment.get_environment()
        env.factory.add_engine('CPORPlanning', 'up_cpor.engine', 'CPORImpl')

        with OneshotPlanner(name='CPORPlanning') as planner:
            result = planner.solve(problem)
            print("%s returned: %s" % (planner.name, result.plan))
