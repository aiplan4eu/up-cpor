# CPOR
CPOR is an offline contingent planner that computes a complete plan tree (or graph) where each node is labeled by an action, and edges are labeled by observations. The leaves of the plan tree correspond to goal states. CPOR uses the SDR translation to compute actions. When a sensing action is chosen, CPOR expands both child nodes corresponding to the possible observations. CPOR contains a mechanism for reusing plan segments, resulting in a more compact graph.

More information about CPOR can be found in the paper: "Computing Contingent Plan Graphs using Online Planning" by Maliah and Shani, published in TAAS in 2021.

# SDR
SDR is an online contingent replanner that provides one action at a time and then awaits to receive an observation from the environment. SDR operates by compiling a contingent problem into a classical problem, representing only some of the partial knowledge that the agent has. The classical problem is then solved. If an action is not applicable due to the partial information, SDR modifies the classical problem and replans.

More information about SDR can be found in the paper: "Replanning in Domains with Partial Information and Sensing Actions" by Brafman and Shani, published in JAIR in 2012.

# Installation

To install 'up-cpor', clone the project and open a command prompt from the project directory on your PC. Then create a new environment with the following command:

```bash
conda create -n up_cpor_env python=3.8.0
conda activate up_cpor_env
```

Finally, use pip to install the required dependencies:

```bash
pip install -r requirements.txt
```
This will install the unified_planning package and all the essential components to run the algorithm.

## Usage

CPOR and SDR can be used in different ways, depending on the specific requirements of your project. Here are some examples:

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

# Notebooks

We provide two example notebooks to demonstrate the usage of CPOR and SDR engines in different settings:

[CPOR_and_SDR_running_examples.ipynb](https://github.com/aiplan4eu/up-cpor/blob/master/Tests/CPOR_engine_demo.ipynb): This notebook contains a full running example on a Windows machine, showcasing the CPOR engine and the SDR engine with a simulated environment. It includes step-by-step instructions and explanations of the code, making it easy to follow along and experiment with the engines.

[CPOR_and_SDR_running_examples_colab.ipynb](https://colab.research.google.com/drive/1e9u9bbjRgBZpF9Trrpu_dcdGgdVFFqwF?usp=sharing#scrollTo=7SMMuaddoPTn): This notebook contains a full running example on Google Colab, showcasing the same engines and the same problem, but running in a cloud environment. This allows you to experiment with the engines even if you don't have a powerful machine or a local Python environment set up.

Both notebooks can be found in the Tests directory of the project repository on GitHub. We recommend starting with the first notebook, which provides a more detailed explanation of the concepts and code, before moving on to the Colab notebook if needed.

We hope these examples will help you get started with using CPOR and SDR engines in your own projects!