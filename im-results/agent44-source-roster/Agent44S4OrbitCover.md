# S4 orbit-cover criterion and q32 witness

Lean 4.36.0-rc2 source: [Agent44S4OrbitCover.lean](Agent44S4OrbitCover.lean), compiled locally.

## Generic criterion

For a safety predicate on partial tables, a symmetry action, and a refinement relation oriented as “child refines parent” (the child cylinder is contained in the parent cylinder), it suffices to prove:

1. Safety is monotone under refinement: a safe parent implies a safe child.
2. Safety transports under each symmetry.
3. Every symmetry has an inverse.
4. For every residual x, some symmetry image of x refines a member of the representative set.
5. Every representative is safe.

The Lean theorem `all_safe_of_orbit_cover` derives safety of every residual. Exact closure of the residual roster under the group action is not required; a safety-direction cover is enough.

## q32 example

Using A..F = Fin 6, symbols 0..1 = Fin 2, and transitions (write, direction, next-state):

- q32/raw11: A0=1RB, B0=1RC, C0=0LA.
- C↔D image: A0=1RB, B0=1RD, D0=0LA; this strictly refines raw152/canonical115 (A0=1RB, B0=1RD).
- C↔E image: A0=1RB, B0=1RE, E0=0LA; this strictly refines raw156/canonical119.
- C↔F image: A0=1RB, B0=1RF, F0=0LA; this strictly refines raw160/canonical123.
- raw152 maps exactly to raw156 under D↔E and to raw160 under D↔F.

Thus this example disproves exact roster invariance but does not disprove a 99-representative safety quotient: the three nonidentity q32 images are covered by the raw152/raw156/raw160 parent orbit. The bridge must verify the refinement-cover condition for every residual and every symmetry image.

## Reproducible audit

`orbit_cover_audit.py` reads the canonical-124 JSON, removes raw residuals 66, 70, and 80 when the input still has 124 entries, generates all 24 permutations fixing A and B, and checks whether each renamed residual refines an exact-orbit representative or any roster entry. It also computes a greedy set-cover upper bound. Greedy output is diagnostic, not an optimality proof; the exact per-image refinement relation is the key evidence.

The audit is deliberately separate from the Lean theorem: Python identifies the finite coverage obligations, while a publishable quotient still needs those obligations reflected in a kernel-checked proof.

The generic cover theorem has no axioms. The finite table/refinement equalities use only Lean core `propext` and `Quot.sound`; there are no project-specific axioms.
