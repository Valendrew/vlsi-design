# SMT model

This directory contains the python script to run the SMT model (both basic and rotation ones).

## Installation
To install and activate the conda environment:
```shell
conda env create -f environment.yml
conda activate unibo-cdmo
```

You also need to install the z3/CVC4 solver on Pysmt, once you installed the conda environment you simply need to run:

```shell
pysmt-install --z3
pysmt-install --cvc4
```
WARNING: the installation of CVC4 on Windows fails due to some bugs in the configuration files, if you want to try CVC4 you should run the project from a Linux environment.

## Usage

You can run the SMT solver using:
```shell
python model.py [-h] [-ins INSTANCE_FILE]|[-test FROM TO] [-rot] [-sol {z3, cvc4}] [-to TIMEOUT] [-search {bin, lbound}]
```

Where:
- -ins is the .txt file of the instance you want to run, e.g. "ins-10.txt"
- -test takes as input the range of instances we want to test and it's in XOR with -ins
- -rot if it's inserted then the rotation model is used
- -sol makes you choose the solver between z3 and cvc4
- -search, the algorithm to use for finding the optimal solution.

The script saves all the found results in the files `../out/[model]/out-N.txt`, a `csv` file with the statistics of the last run and the plots of the solution for each instance at `../out/[model]/plots/ins-N.png`.