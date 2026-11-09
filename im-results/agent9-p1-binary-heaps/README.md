# Exact two-pile transfer representation of P1 inverse shadows

**Agent 9, 9 November 2026.** Intermediate mathematical reduction, locally Lean 4.36.0-rc2 checked with no `sorry` or custom axioms. See [HeapBridge.lean](HeapBridge.lean). This is a new representation of the *exact scalar shadow grammar*, not a complete decision of the six-state P1 machine or BB(6).

## Universal parity-transfer system

On a pair of natural-number piles `(u,e)` consider two partial transitions:

- **L transfer:** if `u` is even, `(u,e) ↦ (u/2, e+u/2+1)`.
- **R transfer:** if `e` is even, `(u,e) ↦ (u+e/2+1, e/2)`.

Both increment `u+e` by one. The rules themselves contain no source parameter, no critical exponent, and no accumulated inverse cost. A transfer is only legal when the halved pile is even.

A scalar inverse shadow node `(L,m,z)` is represented by `(u,e)` when

```text
u is even,
L+m = u+e+4,
z = e+u/2+1.
```

The original P1 feeder roots map to

```text
(L,z)=(16q+8,12q+4) → (u,e)=(8q+2,8q+2)
(L,z)=(16q+9,10q+4) → (u,e)=(12q+4,4q+1).
```

The original exact shadow edge equations are

```text
z = 2^t * v
2*z' + 1 = L+m+t+v
m' = m+t+1.
```

**Formal two-way block correspondence:** From any represented node, each legal exact shadow edge is realized as exactly one L transfer followed by exactly `t` R transfers, ending at another represented node. Conversely, a represented target reached by such a block satisfies the same original scalar equations. The forward and backward propositions are `shadow_step_realized_by_heap` and `heap_block_is_shadow` in the Lean file. `right_run_closed` and `right_run_quotient` establish the exact (unbounded) dyadic quotient identity.

## Unique-parent geometry

After an L transfer the right pile is strictly larger than the left. After an R transfer the left pile is strictly larger than the right. The destination uniquely identifies its legal predecessor:

```text
If U<E, the only possible predecessor is L from (2U, E-U-1).
If E<U, the only possible predecessor is R from (U-E-1, 2E).
If U=E, the destination has no legal predecessor.
```

The unrestricted transfer graph therefore has indegree at most one. This is Lean theorem `heap_edge_predecessor_unique`. Each edge increases the sum by one, so no directed cycles exist. These properties identify a highly constrained universal forest carrying the original scalar inverse dynamics as left-delimited paths.

### Both feeders share a single diagonal origin

There is an exact and particularly useful link between the two originally separate P1 feeder roots. The diagonal seed `(8q+2,8q+2)` has the two legal immediate children

```text
L: (4q+1, 12q+4)
R: (12q+4, 4q+1).
```

The R child is **exactly the second feeder root**. Thus the first feeder begins at a diagonal root, while the second begins one legal transfer below the same root; the left and right children are coordinate reflections. The Lean theorems `feeder_siblings` and `diagonal_no_predecessor` prove this relation and that no diagonal state has any legal parent. Coupled with `heap_edge_predecessor_unique`, this gives a shared root and a uniquely decoded past for the entire universal tree. It may permit coordinated analysis of both genuine P1 feeder obligations through one arithmetic dynamical system.

### Complete backward existence theorem

[HeapForest.lean](HeapForest.lean) strengthens the picture with a *kernel-checked strong-induction theorem*. Every unequal pair `(U,E)` has a legal predecessor of exactly one smaller total pile sum: `(2U,E-U-1)` when `U<E`, and `(U-E-1,2E)` when `E<U`. Iterating backwards must therefore reach a diagonal node `(a,a)` after finitely many steps. The Lean theorem `diagonal_ancestor` constructs a finite `HeapPath` from some diagonal root to **every natural heap pair**. Its local compiler axiom report is `[propext, Quot.sound]`, with no sorry or custom axioms. Together with the unique-parent result, this provides a global forest representation with all roots on the diagonal. This is a backward-well-foundedness theorem; it does not imply finite *forward* branching depth.

## Status and next question

The representation is exact at the scalar recurrence level. It does not by itself establish a direct original raw-Turing-machine correspondence; that connection depends on the independently established P1 `ShadowReach` source bridge and its conditions. The unrestricted heap game supports some infinite paths (for example with a zero left pile), and the prior source margin forces extra restrictions on authentic feeder histories. Accordingly, neither unrestricted heap termination nor P1 halting follows.

The next substantive question is whether a path beginning at either **specified feeder seed** can contain infinitely many left-delimited blocks while remaining at represented states with positive left pile. The unique-parent forest structure could permit arithmetic exclusion of all such paths beyond the already certified eventually-periodic depth cases. To exploit this, derive a quantitative invariant for return-to-even-left boundary states or an exact 2-adic characterization of infinite rays, then import the original P1 `ShadowReach` relation.

Source-certified finite-parameter gateway results from this incarnation live in [../agent9-p1-largecones](../agent9-p1-largecones/); their status is separated from this pure mathematical reduction.
