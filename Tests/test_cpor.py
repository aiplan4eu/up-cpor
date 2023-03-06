from unified_planning.io import PDDLReader
from unified_planning.engines.results import PlanGenerationResultStatus

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
            f"../Tests/DLLs/{prob}/d.pddl",
            f"../Tests/DLLs/{prob}/p.pddl"
        )

        solver = CPORImpl()
        result = solver.solve(problem)

        if result.status == PlanGenerationResultStatus.SOLVED_SATISFICING:
            print(f'{solver.name} found a valid plan!')
            print(f'Success')
        else:
            print('No plan found!')