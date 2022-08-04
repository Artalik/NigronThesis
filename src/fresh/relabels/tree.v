Inductive Tree (X: Type) :=
| Leaf: X -> Tree X
| Node: Tree X -> Tree X -> Tree X.

Arguments Leaf [X] _.
Arguments Node [X] _ _.
