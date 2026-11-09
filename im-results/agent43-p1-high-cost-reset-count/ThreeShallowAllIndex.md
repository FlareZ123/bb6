# Three shallow P1 inverse transitions: exact scalar obstruction at all indices

**Status: original-source proved in Lean 4.36.0-rc2 for the complete three-shallow word language.**
All modules live in `im-results/agent43-p1-high-cost-reset-count/`; no theorem here
establishes a blank-origin halt decision or an exact Busy Beaver value.

## Exact all-index statement

Let `n>=14`, `P=2^n`, `q=8^s`, with `q*p=P`, `q*d=14*n+92`,
`3*s<=n`. For three shallow choices `t_i in {0,1}` set

```
(alpha_i,C_i,L_i,O_i) =
  (1,588,84,232)  when t_i = 0
  (2,392,56,136)  when t_i = 1
A1=2^alpha*8^u; A2=2^beta*8^v; A3=2^gamma*8^r
T1=n+6+3*s
T2=T1+alpha+3*u
T3=T2+beta+3*v
T4=T3+gamma+3*r
R1=L1*T1-O1-d
R2=L2*T2-O2
R3=L3*T3-O3
E=112*T4-384
K=C1*q+C2*q*A1+C3*q*A1*A2-98
```

The integer equation

```
K*p=A1*(A2*(A3*E+R3)+R2)+R1
```

is impossible for **all natural s,u,v,r**, and every `n>=14`, without
enumerating a bounded history length. Lean theorem
`BB6.Agent43ThreeShallowAll.no_three_shallow_numeric_all` in
[ThreeShallowAllNumeric.lean](ThreeShallowAllNumeric.lean) is an all-index proof.
[ThreeShallowAbstractBridge.lean](ThreeShallowAbstractBridge.lean) additionally
proves `no_three_shallow_energies`: the exact three shallow cocycles and the
three depth-two energy-division laws, together with the above root quotients,
imply the inconsistent terminal equality. This removes a large algebraic
obligation from any future original-source induction.

## Proof

For n>=58, [ThreeLayerBarrier.lean](ThreeLayerBarrier.lean) iterates the
positive-remainder divisibility argument three times. The quartic separation

```
13440000000*(n+2)^4 < 2^n  for every n>=58
```

is proved in [ThreeLayerGap.lean](ThreeLayerGap.lean) by an exact four-step
exponential induction. [ThreeLayerPeel.lean](ThreeLayerPeel.lean) supplies
the nested integral quotient lemma and
[ThreeShallowNumeric.lean](ThreeShallowNumeric.lean) converts the exact
coefficient ranges into the abstract obstruction.

For 14<=n<58, `q | (14*n+92)` forces `s<=3`. The exact equation gives
the integer first numerator `N1=A1*(C2*P-R2+A2*(C3*P-R3-A3*E))` via
[ThreeShallowIntegerAlgebra.lean](ThreeShallowIntegerAlgebra.lean).
If u>=3, then `2^alpha*512 | N1`, contradicting the exact finite
`first_overflow_false_58` certificate. After dividing by A1, the next
numerator is `N2=A2*(C3*P-R3-A3*E)`. The second finite certificate forces
v<=2. One further division gives `N3=-A3*E`; the third finite
certificate forces r<=2. Then `no_three_small_bad_58` excludes the
remaining exact equation. All four fixed-index certificate families are
in [ThreeShallowFiniteBounds.lean](ThreeShallowFiniteBounds.lean), with
the quantified Boolean-to-Prop bridges in
[ThreeShallowFiniteBridge.lean](ThreeShallowFiniteBridge.lean).

The symbolic high-index theorem compiled in original-source dependency
[CI 42540466503](https://github.com/FlareZ123/bb6/actions/runs/42540466503).
The all-index arithmetic theorem compiled in
[CI 42542068055](https://github.com/FlareZ123/bb6/actions/runs/42542068055),
with `#print axioms` showing only
`[propext, Classical.choice, Quot.sound]`. The abstract bridge compiled in the full repository workflow [CI 42542712348](https://github.com/FlareZ123/bb6/actions/runs/42542712348), no `sorryAx`. This certifies the exact cocycle interface, **not** a fully source-lifted three-shallow `inverseAt` word theorem.

## Verified unchanged-original-source theorem

[SourceOneShallowLift.lean](SourceOneShallowLift.lean) proves
`BB6.Agent43SourceWord.source_no_three_shallow_word_wall_all`: no
legal original `inverseAt` history from the critical P1 source
`(14*2^n-2*n-16,3,0)`, with n>=14 and depth word
`(2)^s (0|1) (2)^u (0|1) (2)^v (0|1) (2)^r`,
can terminate at the exact shifted wall
`b+4*m+4*n+20=12*2^n`. Every inverse edge is constrained by its
original parity, inverse-value, left-bound and output-bound hypotheses.
The four runs can be arbitrarily long, and all eight choices of three
shallow depths are included. No finite-run assumption is introduced.

[ThreeShallowSourceModel.lean](ThreeShallowSourceModel.lean) first proves
`no_three_shallow_model_from_source_coefficients`: four exact `TwoRun`
relations, three affine `I`-energy cocycles, and the final wall give
the arithmetic contradiction. It derives the exact 8-adic root quotients,
the positive natural remainders, the nested wall equation and cost identity.
The source theorem then calls original `two_chain_mass` and
`two_chain_model` for all four blocks, original `inverseAt_iff_power_mass`
for all three shallow edges, and `source_shallow_profile` for their
true coefficients before invoking the model theorem.

The **full original-source proof compiled successfully** in
[manual GitHub Actions CI 42544621231](https://github.com/FlareZ123/bb6/actions/runs/42544621231).
Its final `#print axioms` is
`[propext, Classical.choice, Quot.sound]`; there is no `sorryAx`.
The previously established all-index arithmetic and abstract bridge
are also included in this run. This is the strongest current verified
source word exclusion in this dossier.

## Consolidated low-depth source language

[SourceLowDepth.lean](SourceLowDepth.lean) adds a complete inductive
`SourceLowTrace` for all finite legal original `inverseAt` histories
whose inverse depths are restricted to `0,1,2`. The induction records the
exact count `z` of depth-0/1 transitions and constructs a decomposition
into arbitrarily long depth-two runs. Its source theorem

```lean
source_low_trace_wall_needs_four_shallows :
  SourceLowTrace n z (14*2^n-2*n-16) 3 0 b d m →
  b+4*m+4*n+20=12*2^n → 4≤z
```

holds for every `n>=14`. The zero-shallow case follows from the
positive critical-root affine defect `I`, its exact division by
`8^s` on depth-two runs, and negative `I` on the wall.
The one-, two-, and three-shallow cases instantiate the separately
original-source-certified word theorems.

Original-source [CI 42546553574](https://github.com/FlareZ123/bb6/actions/runs/42546553574)
successfully checked the full chain. Its final axiom list is
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
The theorem is a uniform necessary condition on actual bounded-depth
inverse paths, with no length, cost or shallow-edge ordering restriction.

## Open quantifiers and next mathematical frontier

An actual P1 halting decision remains open. The next candidate grammar
contains four shallow transitions, with arbitrary depth-two gaps; more
general inverse words also permit depth >=3 and exceptional exits. The
present theorem restricts only histories that satisfy its explicit
`SourceTwoChain` decomposition. It does not prove an authentic
blank-root reachability/exclusion statement or a BB(6) maximality result.

A general symbolic (k)-shallow remainder theorem, with a formal
source-word lift and a nontrivial parameter-uniform conclusion, is the
most promising extension. Additional finite scans of already excluded
three-shallow words would duplicate the proved result. These results
remain under `im-results/` pending external novelty qualification.
