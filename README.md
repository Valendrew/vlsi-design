# Combinatorial and Decision Making (CDMO) project work  (AY 2021/2022)

The project work involves solving the chosen problem using:

- Constraint Programming (CP)
- Propositional SATisfiability (SAT) or Satisfiability Modulo Theories (SMT)
  - Bonus point for doing both
- Mixed-Integer Linear Programming (MIP)

A set of problem instances is provided, but assumptions should not be made based on them.

## CP and SAT

Use MiniZinc and Z3 solvers.

Advices:

1. Start with the problem parameters, decision variables, the main problem constraints and the objective function
2. Constraint the objective function with tight lower and upper bounds
3. Consider different SAT encodings to reduce the encoding size
4. Investigate if there are any implied constraints that one can benefit form
5. Use global constraints to impose the main problem constraints and the implied constraints in the CP model
6. Observe if any symmetry can be exploited to improve the CP model and the SAT encoding by adding symmetry breaking constraints. Note that when you enforce multiple symmetry breaking constraints, they should not conflict with each other (i.e., there must be at least one solution satisfying all the symmetry breaking constraints)
7. Investigate the best way to search for solutions in CP which does not conflict with the symmetry breaking constraints. The symmetry breaking constraints should not conflict with the SAT search either.

## SMT and MIP

Use favourite solvers and languages (excluded MiniZinc)

Bonus point if the problem is encoded with solver-independent languages

- Try different solvers without rewriting the model

A solver can take advantage of a solution computed by another solver

## Final remarks

Solving processes that exceed a time limit of 5 minutes should be aborted

- Ones too difficult to be solve within the time limit can be avoided: it is not necessary to succeed in solving all instances

## Folder structure

- *~/out/*: output files of those instances that could be solved successfully
  - Output files name with a corrispondence to the related input file
- *~/src/*: source code
- *README*: basic instructions for execution
