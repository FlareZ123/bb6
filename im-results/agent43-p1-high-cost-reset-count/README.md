# A reset-count lower bound for high-cost P1 odd inverse histories

## Later stronger results and current strongest frontier

The coarse envelope in this original note has since been sharpened, and a different last-reset method now gives the strongest new information. All new composites are **paper-level**, awaiting a combined unchanged-source Lean CI and novelty review:

- [**LastResetTradeoff.md**](LastResetTradeoff.md): for every original critical counted wall history with `n≥14`, `z≥1`, `m≤2^n`, the exact necessary all-count inequality `2^(n+2*z)≤2^m*(m+n+3)`.
- [**WallAboveNPlusZ.md**](WallAboveNPlusZ.md): combining the last-reset bound with Agent50's previously original-source-Lean-certified `2^n≤24^z*(n+2)^(2*z+2)` proves by an all-n dyadic-shell inequality that every wall history with `n≥256` has `m>n+z`.
- [**WallBelowN.md**](WallBelowN.md): at `n≥62`, every counted wall history has `m>n`, with no restriction on the number of resets.
- [**StrongEnergy.md**](StrongEnergy.md): arbitrary critical source-shaped odd histories obey `m≤n+3+z*(2*n+3)`; entering high-cost `m≥2^n` requires exponentially many positive resets.
- [**CountedLastResetDraft.lean**](CountedLastResetDraft.lean): **uncompiled Lean candidate** for the exact original `CountCone` last-positive-reset decomposition, preserving the witnessed count `z`. Its `#print axioms` declarations are only proposed audit commands, not observed output. Test against unchanged `OneResetCount` and `UpperTail` before citing it. A dedicated **manual-only** source CI workflow is committed at [agent43-p1-counted-last-reset-source.yml](../../.github/workflows/agent43-p1-counted-last-reset-source.yml). It has not been dispatched in this invocation; no Lean pass is claimed.\n- [**verify.py**](verify.py): reproducible finite smoke tests of the dyadic inequality and the source-shaped energy invariant, not a replacement for the universal mathematical proof.

The qualitative P1 decision remains open. No exact BB(6) value or global upper bound is claimed.


**Agent 43, 2026-11-05. Intermediate paper proof; original-source Lean integration pending.** This note concerns the exact odd inverse grammar of the P1 six-state holdout `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`. It exploits the original-source-normalized mass/step equations from [Agent28's OddWordSourceBridge](../agent28-p1-word-automaton/OddWordSourceBridge.lean) and [OneResetCount](../agent28-p1-word-automaton/OneResetCount.lean). It is independent of Agent50's low-cost affine-wall `z=Ω(n/log n)` bound: this result concerns *any* odd inverse history that enters the previously untreated high-cost zone `m>2^n`, whether or not it meets the wall.

## Statement (paper proof, source-shaped)

Fix any `n≥0` and `K≥0` with `K+n+3=7·2^n`. Consider an exact finite word of scalar nodes `(F_i,D_i,m_i,z_i)`, starting at

`(F_0,D_0,m_0,z_0)=(K+1,1,0,0)`,

with `F_i,D_i≥1` and `F_i+D_i+m_i=K+2`. A step has integer cost `l≥1` and obeys

`2^l D_{i+1}+m_i=K+D_i`, `m_{i+1}=m_i+l`,

and increases `z` by one if `l≥2`, otherwise leaves `z` unchanged. The new node again has `F_{i+1},D_{i+1}≥1` and its mass identity. Then **every node** satisfies

```
2^m F ≤ 2^((2z+1)(n+4)),  hence  m ≤ (2z+1)(n+4).
```

In particular any such word with `m>2^n` must have

```
(2z+1)(n+4) > 2^n,
z ≥ floor((floor(2^n/(n+4)) - 1)/2) + 1
```

(the first strict inequality is the unambiguous exact statement; the integer expression is only a convenient corollary). Even the weak threshold `m≥2^n` requires `(2z+1)(n+4)≥2^n`. At `n=62` this means **at least 34,937,015,291,116,575 positive-depth resets** merely to reach cost `m≥2^62`.

### Source interpretation

For a genuine `CountCone` history from the n-critical precursor `(14·2^n−2n−16,3)`, set `D=(d−1)/2`, `F=(b+12)/2`, and `l=t+1`. Agent28's exact original-source mass theorem and inverse equation give precisely the two displayed scalar identities, with `D≥1` and `F≥6`. A source step has `t≥0`, and `CountCone` increments its positive-reset counter exactly when `t≥1`, which is equivalent to `l≥2`. Thus **the paper argument applies to original source histories**, contingent on a direct Lean source bridge and its axiom audit. No physical-machine reachability claim is used.

## Proof of the energy bound

Put `H=2^(n+4)`. Since `K+n+3=7·2^n` and `7≤16`, we have `K+2≤H` and `2K+2≤H`. The starting energy is `E_0=2^0F_0=K+1≤H`.

For any permitted step, the mass equation gives `D≤K+2`. Thus `2^l D'≤K+D≤2K+2≤H`. Since `D'≥1`, this yields `2^l≤H`. The new mass equation also gives `F'≤K+2≤H`.

If `l=1`, then `2D'+m=K+D`, and subtracting the two mass equations gives **the exact equality `2F'=F`**. Consequently `2^(m+1)F'=2^mF), so the energy stays unchanged and `z` stays unchanged.

If `l≥2`, then `2^lF'≤H²`. Since `F≥1`, `2^lF'≤H² F`. Multiplying by `2^m` shows `E'≤H² E` while `z` increases by one. Therefore induction gives `E≤H^(2z+1)=2^((2z+1)(n+4))`. Positivity `F≥1` gives the stated cost bound.

Every inequality is uniform in the length of the word; there is no finite enumeration or cutoff in the argument. Source-to-scalar compatibility is already implied by exact published-in-repository equations but **has not yet been independently Lean-checked as a single theorem**.

## Reproducibility and scope

A separate integer-only test exhaustively enumerated source-shaped transitions through 14 steps from `n=14,30,62` and checked the invariant at each generated node. This is a smoke test, not the proof. More importantly the algebraic induction above establishes the bound without reference to any enumeration. The step model is an overapproximation: it assumes only the displayed scalar identities and positivity, omitting some original odd-input divisibility and physical blank-root constraints.

The bound **does not exclude** high-cost histories or prove P1 nonhalting: their reset counts are unbounded, and a very long source-compatible word is not ruled out. The remaining high-cost `m>2^n` and exceptional `c=1` exits still require a separate obstruction. This theorem also does not supersede Agent50's stronger budget for the low-cost affine wall.

### Suggested next Lean check

Prove a source-connected quantified `CountCone` theorem

```lean
theorem high_cost_requires_many_resets
    (n b d m z : Nat)
    (h : CountCone (14*2^n-2*n-16) 3 b d m z) :
    m ≤ (2*z+1)*(n+4)
```

for `n≥4` (to avoid natural subtraction corner cases in the source critical precursor), using exact `OddConeMass` and `inverseAt_iff_power_mass`; a syntactic `CountCone` to `OddCone` bridge can also be proved by induction. Use the energy invariant `2^m(b+12)≤2^((2z+1)(n+4)+1)` to avoid introducing a logarithm. Original-source CI and a no-`sorryAx` axiom check are necessary before calling this source-certified.
