# Formalization of a Structurally Recursive Version of a Incremental Algorithm for Convex Hull in Coq

Christophe Brun, Jean-François Dufourd, Nicolas Magaud

This provides a formalization of the incremental algorithm to compute 2D convex hulls using combinatorial maps.
This implementation relies on the inductive structure of hypermaps to compute recursively the new convex hull at each step. 
It allows to have structurally recursive computations only. However it does not fully take advantage of the geometric properties of the convex hull.

Related publication : https://hal.archives-ouvertes.fr/hal-00955400

It compiles with Coq 8.10.2.