from unified_planning.io import PDDLReader
from up_cpor.engine import CPORImpl

if __name__ == "__main__":

    # Creating a PDDL reader
    reader = PDDLReader()

    # Parsing a PDDL problem from file
    problem1 = reader.parse_problem(
        "../Tests/DLLs/doors5/d.pddl",
        "../Tests/DLLs/doors5/p.pddl"
    )

    solver = CPORImpl()
    result = solver.solve(problem1)