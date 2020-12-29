# Specimen test

## Group I
### Question 1
* A) An instance **will** be found. For example, when **r[A3] = B2**.
* B) An instance **will** be found. For example, if there are **no relations** between A and B.
* C) An instance **will** be found. For example, when r.B2 = {(A1),(A2),(A3)}
* D) An instance **will not** be found. Since there are 3 A signatures, and each of them must be at least associated with 1 B, and there are only 2 B signatures, that means we cannot guarantee that for each B there is only one A at most.
* E) An instance **will not** be found. By the model's restrictions we know that (A1, B1) and (A2, B1) are present in the relation R. Therefore, the restriction that each B has associated at most one A will not happen.
* F) An instance **will not** be found. Since r.B1 = r.B2, and B's most be associated with at least one A, that means that exists an A (a1,a2 or a3) that is associated with the B1 and B2, therefore, the lone restriction will fail.

## Group II
### Question 1
* A) The **analysis variables** are:
- the signatures: Node, DAG
- the field *edge*, and
- the three arguments to the *add* predicate: g, g', e

* B) The **analysis constraint** for the command are:
- the body predicate being run: one e, g'.edge = g.edge + e
- the explicit facts: all g: DAG | no n: Node | n in n.^(g.edge)
- the constraints implicit in field and arguments declaration: g: DAG, g': DAF, e: Node->Node, edge: DAG->Node->Node
- the constraints implicit in the signatures: no DAG & Edge