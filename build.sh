#!/bin/bash

# requires `conda install -c conda-forge dotnet`
dotnet build CPORLib/CPORLibSolution.sln

pip uninstall -y up-cpor
pip install .
