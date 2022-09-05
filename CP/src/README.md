# Constraint programming model

This directory contains the python script to run the constraint programming model (both basic and rotation ones).

## Installation
To install and activate the conda environment:
```shell
conda env create -f environment.yml
conda activate unibo-cdmo
```

## Usage
You can run the CP solver using the python version of the anaconda environment:
```shell
python model.py [-h] [-ins INSTANCE_NAME]|[-test FROM TO] [-m {base, rotation}] [-s {gecode, chuffed}] [-f] [-t TIMEOUT]
```

Where:
- -ins is the name of the instance you want to run, e.g. "ins-10"
- -test takes as input the range of instances we want to test and it's in XOR with -ins
- -m checks if you want to run the basic or the rotation model
- -s makes you choose the solver between gecode and chuffed
- -f is to activate the free search.

The script saves all the found results in the files `../out/[model]/out-N.txt`, a `csv` file with the statistics of the last run and the plots of the solution for each instance.