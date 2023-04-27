# Spatio-Temporal Reasoner / Automaton

We initialize a grid of theories by adding propositional axioms (atomic propositions with negation and rules) to them. Then the theories transmit their axioms with every timestep to neighboring theories. If a theory becomes inconsistent, i.e. at some point in time contains both an atomic proposition and its negation, it resets to an empty theory.

There is a special proposition which states that a theory is a boundary, i.e. it does neither receive nor transmit axioms. The boundary of the grid is automatically assigned to be theories with the boundary proposition.

The initialization is read from ``grid.txt`` in the following format:
```
<number of columns> <number of rows>
<x_1> <y_1> <Axiom>
<x_2> <y_2> <Axiom>
...
```
For example:
```
10  10
1 1 phi
8 8 NOT(phi)
5 4 BOUNDARY
4 5 BOUNDARY
5 5 psi:-phi
```
