# AI Agent Instructions

This repository contains a mixed Python and C# project. When operating autonomously, follow these guidelines:

## Environment Setup
- **Python**: Use the provided Conda environment `environment.yml`.
- **C#**: Install `dotnet` for compiling the solution and `mono` for running the executables.
- **Testing**: Tests use the `pytest` package. To test meta planners, you must install the `up-tamer` and `up-pyperplan` Python packages.

## Development Workflow
- **Recompilation is mandatory**: You MUST run `./build.sh` after making *any* modifications to the code for the changes to take effect.