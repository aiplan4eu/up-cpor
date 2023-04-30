# CPOR
CPOR is an offline contingent planner.
It computes a complete plan tree (or graph) where each node is labeled by an action, and edges are labeled by observations.
The leaves of the plan tree correspond to goal states.
CPOR uses the SDR translation to compute actions.
When a sensing action is chosen, CPOR expands both child nodes corresponding to the possible observations.
CPOR contains a mechanism for reusing plan segments, resulting in a more compact graph.
Complete information can be found at the followign paper: Computing Contingent Plan Graphs using Online Planning, Maliah and Shani,TAAS,2021.

# SDR

SDR is an online contingent replanner
It provides one action at a time, and then awaits to receive an observation from the environment.
SDR operates by compiling a contingent problem into a classical problem, representing only some of the partial knowledge that the agent has.
The classical problem is then solved. If an action is not applicable, due to the partial information, SDR modifies the classical problem and replans.
Complete information can be found at the followign paper: Replanning in Domains with Partial Information and Sensing Actions, Brafman and Shani, JAIR, 2012.'

# Installation

After cloning the project open cmd from the project dir in you PC and create new env:

```bash
conda create -n up_cpor_env python=3.8.0
conda activate up_cpor_env
```

Use the package manager [pip](https://pip.pypa.io/en/stable/) to install up-cpor.

```bash
pip install -r requirements.txt
```
It will install the unified_planning package and all the essential to run the algorithm. 

## Usage

### CPOR Engine

```python
import unified_planning.environment as environment
from unified_planning.shortcuts import OneshotPlanner

env = environment.get_environment()
env.factory.add_engine('CPORPlanning', 'up_cpor.engine', 'CPORImpl')

with OneshotPlanner(name='CPORPlanning') as planner:
    result = planner.solve(problem)

```

### CPOR Meta Engine

```python

import unified_planning.environment as environment
from unified_planning.shortcuts import OneshotPlanner

env = environment.get_environment()
env.factory.add_meta_engine('MetaCPORPlanning', 'up_cpor.engine', 'CPORMetaEngineImpl')

with OneshotPlanner(name='MetaCPORPlanning[tamer]') as planner:
    result = planner.solve(problem)

```

### SDR Engine - with UP Simulated Environment

```python
import unified_planning.environment as environment
from unified_planning.model.contingent.environment import SimulatedEnvironment
from unified_planning.shortcuts import ActionSelector

env = environment.get_environment()
env.factory.add_engine('SDRPlanning', 'up_cpor.engine', 'SDRImpl')

with ActionSelector(name='SDRPlanning', problem=problem) as solver:
    simulatedEnv = SimulatedEnvironment(problem)
    while not simulatedEnv.is_goal_reached():
        action = solver.get_action()
        observation = simulatedEnv.apply(action)
        solver.update(observation)

```

### SDR Engine - with SDR Simulated Environment

```python
import unified_planning.environment as environment
from unified_planning.shortcuts import ActionSelector

from up_cpor.simulator import SDRSimulator


env = environment.get_environment()
env.factory.add_engine('SDRPlanning', 'up_cpor.engine', 'SDRImpl')

with ActionSelector(name='SDRPlanning', problem=problem) as solver:
    simulatedEnv = SDRSimulator(problem)
    while not simulatedEnv.is_goal_reached():
        action = solver.get_action()
        observation = simulatedEnv.apply(action)
        solver.update(observation)

```

#Notebooks

There are 2 examples: 
1) Full running example on Windows settings [CPOR_and_SDR_running_examples.ipynb](https://github.com/aiplan4eu/up-cpor/blob/master/Tests/CPOR_engine_demo.ipynb)
2) Full running example on Google Colab settings [CPOR_and_SDR_running_examples_colab.ipynb](https://github.com/aiplan4eu/up-cpor/blob/master/Tests/CPOR_and_SDR_running_examples_colab.ipynb)