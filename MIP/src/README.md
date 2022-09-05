# Mixed Integer Programming model

This directory contains the python script to run MIP models:

- PuLP model: both base and rotation are available
- Minizinc model: only base is available

## Installation

To install and activate the conda environment:

```shell
conda env create -f environment.yml
conda activate unibo-cdmo
```

You also need to install [CPLEX Optimizer](https://www.ibm.com/analytics/cplex-optimizer) (v. 22.1.0) and configure the environment variables for [PuLP](https://coin-or.github.io/pulp/guides/how_to_configure_solvers.html#cplex)

Mosek is already installed with version 10.0.18

For the Minizinc model is necessary an [additional step](https://www.minizinc.org/doc-2.6.4/en/command_line.html) to configure CPLEX.

## Usage

You can run the MIP solver from the root folder using:

```shell
python MIP/src/model.py [-h] [-ins INSTANCE_FILE]|[-test FROM TO] [-m {base rotation}] [-s {cplex, mosek, minizinc}] [-t TIMEOUT] [-v]
```

Where:

- -ins is the file of the instance you want to run
- -test takes as input the range of instances we want to test and it's in XOR with -ins
- -m the model type, base or rotation
- -s makes you choose the solver between cplex, mosek and minizinc

The script saves all the found results in the files `../out/[model]/out-N.txt`, a `csv` file with the statistics of the last run and the plots of the solution for each instance at `../out/[model]/plots/ins-N.png`.
