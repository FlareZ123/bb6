# Original P1 feeders: no eventually constant inverse-depth ray

**Agent 13, 6 November 2026.** Complete pinned Lean 4.36.0-rc2 source verification: [GitHub Actions run 42314919290](https://github.com/FlareZ123/bb6/actions/runs/42314919290), successfully rebuilding and importing the unchanged original P1 inverse-shadow chain. The proof relies only on standard Lean axioms `[propext, Classical.choice, Quot.sound]`, and uses neither `sorry` nor `native_decide`. These are **intermediate structural theorems**, not a full P1 halting decision or a Busy Beaver proof.

## Exact mathematical statement

Take the source-verified scalar inverse predecessor equation, for fixed `L` and cumulative inverse cost `m`:

```text
z = 2^t*v,      2*z' + 1 = L+m+t+v,
m' = m+t+1.
```

Every genuine P1 feeder shadow path begins at one of

```text
L0=16q+8, z0=12q+4,
L1=16q+9, z0=10q+4.
```

The original-source terms `BB6.Precision.ShadowReach L0 z0 m z` and `ShadowReach L1 z0 m z` are imported unchanged from `UniformPrecisionPath.lean`. [SourceHomogeneous.lean](SourceHomogeneous.lean) establishes, for **every** `q,m,z,t`, that any genuine feeder shadow state `(m,z)` cannot have `N` subsequent edges all of the same fixed depth `t` for **every** natural `N`:

```lean
BB6.Agent13RootHomogeneous.source_feeder0_no_homogeneous_ray
BB6.Agent13RootHomogeneous.source_feeder1_no_homogeneous_ray
```

Quantifier scope matters: arbitrary mixed or eventually nonperiodic inverse-depth sequences remain possible. These theorems do not show that the complete source inverse graph is finite. Excluding infinite homogeneous rays, by itself, does not exclude a critical gateway or resolve the P1 machine.

## All positive dyadic depths, with an explicit length certificate

In [FixedDepthGeneral.lean](FixedDepthGeneral.lean), for any fixed `t≥1`, let

```text
h=2^t,  A=2h=2^(t+1),  d=A-1,  s=t+1,
u=L+m+t-1,
Phi_t(L,m,z)=d^2*z - h*d*u + A*h*s.
```

The exact edge equations yield `A*z'=z+h*u` and `u'=u+s`. A Lean-proved polynomial identity therefore gives

```text
A * Phi_t(L,m+t+1,z') = Phi_t(L,m,z).
```

The potential is **never zero for integers** `L,m,z` when `t≥1`. If it were zero, the identity modulo `d` would force `d | h*s`. The relations `A=d+1=2h` force `d | s`. But `0<s=t+1<2^(t+1)-1=d`, a contradiction. This proof is checked in Lean using exact divisibility and exponential inequalities rather than a floating approximation.

By induction over `N` consecutive true scalar edges of depth `t`, the original nonzero integer potential is divisible by `A^N`. Thus

```text
2^((t+1)*N) ≤ |Phi_t(L,m,z)|.
```

The source theorem `no_infinite_fixed_depth` prohibits an arbitrarily long homogeneous positive-depth ray from **any** concrete shadow node, even without P1's feeder root restrictions.

## Depth zero and original feeder reachability

A distinct phenomenon occurs at `t=0`. The scalar recurrence admits an abstract infinite zero-depth ray on the wall `z=L+m-3`, so the positive-depth argument cannot extend unconditionally. The source-authentic feeder roots satisfy

```text
z0+4≤L.
```

[ZeroDepth.lean](ZeroDepth.lean) proves the margin `z+4≤L+m` is preserved under **every exact inverse edge of any depth**, starting from such a root. This rules out the exceptional `t=0` fixed wall at all genuine feeder-shadow nodes.

The integer `Phi_0=L+m-z-3` is strictly positive on these nodes and obeys `2*Phi_0(m+1,z')=Phi_0(m,z)` at each `t=0` predecessor edge. Thus an `N`-edge zero-depth run from a genuine feeder shadow state satisfies

```text
2^N ≤ Phi_0(L,m,z).
```

[ZeroDepthSource.lean](ZeroDepthSource.lean) transports the preserved margin directly from the exact `BB6.Precision.ShadowReach` source constructors for **both** P1 feeder formulas. [SourceHomogeneous.lean](SourceHomogeneous.lean) composes these two cases into an all-natural theorem for every fixed `t≥0`. The full source audit succeeded in [CI 42314919290](https://github.com/FlareZ123/bb6/actions/runs/42314919290). The independent positive-depth source ran successfully in [CI 42314423200](https://github.com/FlareZ123/bb6/actions/runs/42314423200), while the zero-depth source bridge passed independently in [CI 42314692184](https://github.com/FlareZ123/bb6/actions/runs/42314692184).

## Research leverage and remaining obstruction

The theorem excludes a complete family of tempting infinite-ray escape mechanisms in the original P1 two-feeder inverse grammar. Any genuinely infinite scalar inverse path would necessarily have infinitely many depth changes (unless its positive-depth pattern is unbounded or otherwise mixed). This moves attention to variable-depth, eventually periodic and nonperiodic shadow paths, plus authentic blank-root entry restrictions.

One possible extension is to derive finite-word potentials. For a fixed depth word of total inverse cost `S`, the block recurrence takes the form `A*z'=z+H*(L+m)+D`, `m'=m+S`, `A=2^S`. Its candidate potential is `(A-1)^2*z-H*(A-1)*(L+m)-D*(A-1)+A*H*S`. Proving nonzero for all admissible nontrivial depth words would exclude eventual periodic-depth scalar rays; this broader statement has **not** been proved. A bounded arithmetic exploration through cost `S≤2048` found no nontrivial candidate passing the required divisibility conditions, but this is computational evidence only, without a formal completeness claim for all words.

No theorem here decides all six-state machines, gives a new global Busy Beaver step upper bound, or proves the exact BB(6) value.
