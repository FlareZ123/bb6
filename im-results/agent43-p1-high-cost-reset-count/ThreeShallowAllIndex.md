# Three shallow P1 inverse transitions: exact scalar obstruction at all indices

**Status: arithmetically proved in Lean 4.36.0-rc2, original-source lift pending.**
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
`[propext, Classical.choice, Quot.sound]`. The abstract bridge compiles
locally under Lean 4.36.0-rc2 with no `sorry`; the source CI for its exact
committed bytes is [run 42542712348](https://github.com/FlareZ123/bb6/actions/runs/42542712348).

## Unresolved machine-level step

The theorem is about exact scalar equations that match the original-source
two-step and shallow cocycle formulas. **No three-shallow genuine `inverseAt`
word exclusion has yet been asserted**. To obtain one, re-use
`SourceOneShallowLift.lean`:

1. Construct three `source_shallow_profile` instances around four
   `SourceTwoChain` runs, keeping all original legality/mass assumptions.
2. Apply `two_chain_model` to each run to get the exact `TwoRun` models.
3. Apply `run_cost` and `run_energy` to produce B1/B2/B3 and integer
   energy relations, and `root_two_prefix_divisor` to produce the
   exact `q,p,d` quotients. The latter also gives 3*s<=n.
4. Substitute the root defect `98*P-(14*n+92)`, terminal wall defect
   `-E`, and all three `source_shallow_profile` identities.
5. Invoke `BB6.Agent43ThreeShallowAbstract.no_three_shallow_energies`.
   Its hypotheses are intentionally a thin exact-cocycle interface.

This is a genuine next mathematical bridge, rather than a request to rerun
the finite searches or rederive the quartic gap. All future source lifts
should retain `results/` only for externally publishable advances; this
dossier remains in `im-results/`.
