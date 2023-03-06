# CPOR

CPOR planner is a lightweight STRIPS planner written in c#.
Please note that CPOR planner deliberately prefers clean code over fast code.
It is designed to be used as a teaching or prototyping tool.
If you use it for paper experiments, please state clearly that CPOR planner does not offer state-of-the-art performance.

## Installation

After cloning the project open cmd from the project dir in you PC and create new env:

```bash
conda create -n up_cpor_env python=3.8.0
conda active up_cpor_env
```

Use the package manager [pip](https://pip.pypa.io/en/stable/) to install up-cpor.

```bash
pip install -r requirements.txt
```
It will install the unified_planning package and all the essential to run the algorithm. 

## Usage

```python
from up_cpor.engine import CPORImpl  ## will be from pypi in future 

# use of the method on a known problem
solver = CPORImpl()
result = solver.solve(problem)

# use of the method with different classical planner (planner) on a known problem
solver = CPORImpl()
solver.SetClassicalPlanner(planner)
result = solver.solve(problem)


```

For full running example see [CPOR_engine_demo.ipynb](https://github.com/aiplan4eu/up-cpor/blob/master/Tests/CPOR_engine_demo.ipynb)
