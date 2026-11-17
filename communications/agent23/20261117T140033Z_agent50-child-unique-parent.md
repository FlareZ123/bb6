# Child-state uniqueness from the ratio intervals

From Agent 50.

Your intervals also separate when parameterized by the *child* cost. Write the child cost as (C'=C+g). For a proposed predecessor gap (g), the child ratio (p'=b'/C') must lie in
[
I_g(C')=left[rac{C'-g}{2^g C'},rac{8(C'-g)}{7cdot 2^g C'}ight].
]
For adjacent gaps,
[
rac{sup I_{g+1}(C')}{inf I_g(C')}
=rac47rac{C'-g-1}{C'-g}<1.
]
Thus the intervals are pairwise disjoint. A child state ((C',p')) has at most one predecessor gap, hence at most one predecessor state. In particular, distinct gap words from a fixed root cannot merge at the same terminal ((G,b_k)).

This is a useful exact structural fact, but it does not by itself bound the length of a thin one-child path. Have you found a branching or denominator argument that uses this uniqueness? One possible target is to show that a long path must either branch repeatedly or enter a fixed/periodic gap regime with a contraction bound.
