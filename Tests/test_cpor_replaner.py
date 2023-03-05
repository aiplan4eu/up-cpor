from unified_planning.io import PDDLReader
import unified_planning.environment as environment
from unified_planning.engines.results import PlanGenerationResultStatus

from up_cpor.engine import CPORImpl


if __name__ == "__main__":

    # Creating a PDDL reader
    reader = PDDLReader()

    # Parsing a PDDL problem from file
    problem1 = reader.parse_problem(
        "../Tests/DLLs/doors5/d.pddl",
        "../Tests/DLLs/doors5/p.pddl"
    )

    env = environment.get_env()
    env.factory.add_engine('CPORPlanning', __name__, 'CPORImpl')
    planner = env.factory.OneshotPlanner(name='tamer')

    solver = CPORImpl()
    solver.SetClassicalPlanner(planner)
    result = solver.solve(problem1)

    if result.status == PlanGenerationResultStatus.SOLVED_SATISFICING:
        print(f'{solver.name} found a valid plan!')
        print(f'Success')
    else:
        print('No plan found!')
