# A reset-count lower bound for high-cost P1 odd inverse histories

## Genuine original-source all-reset cost-sector exclusion, n >= 148 (fully certified)

**2026-11-05 22:55 UTC: complete source-connected Lean theorem succeeded.** [Original-source manual CI run 42125396876](https://github.com/FlareZ123/bb6/actions/runs/42125396876), job 127588157490, rebuilt unchanged Agent1/28/47 P1 definitions and authenticated SHA256-extracted Agent50 reset-count sources. Final axiom audit for `BB6.Agent43Wall148Source.source_critical_wall_cost_above_n_plus_resets` is exactly `[propext, Classical.choice, Quot.sound]`.

For **all natural n>=148** and every genuine `CountCone (14*2^n-2*n-16) 3 b d m z`, if the final inverse hub is on the P1 critical affine wall `b=4*(m+n)`, then **`n+z<m`**. The theorem is uniform in every finite positive-depth count z and arbitrary zero-depth interludes. The original source full argument lives in [CountedWall148Source.lean](CountedWall148Source.lean), combining source [CountedWallStrongGateSource.lean](CountedWallStrongGateSource.lean) (`3*2^z<=2*(m+n+3)` when `m<=n+z`), Agent50 [WallCountLowerBound.lean](../agent50-p1-two-reset/WallCountLowerBound.lean) (`2^n<=24^z*(n+2)^(2*z+2)`), and a **fully universal** separate numeric Lean proof [NumericBridge148.lean](NumericBridge148.lean), [NumericPower148.lean](NumericPower148.lean), [NumericShell.lean](NumericShell.lean). The numerical proof was also independently kernel-checked at [pure-numeric CI 42125134569](https://github.com/FlareZ123/bb6/actions/runs/42125134569). An explicit all-integer five-block decomposition and infinite dyadic-shell bound eliminate the previous paper-level original-source gap. Historical [WallAboveNPlusZ148.md](WallAboveNPlusZ148.md) has been marked with the formal status update.

**Scope:** this eliminates a uniform affine-wall cost sector and is meaningful mathematical advancement inside this P1 model, but it neither settles higher-cost affine-wall histories nor exceptional exits, P1 nonhalting, or BB(6). No promotion to `results/` without human novelty/root relevance review.

## Source-kernel verified 2026-11-05: the arbitrary-history energy theorem

The previously paper-only high-cost energy mechanism now has a true unchanged-original-source Lean proof in [CountedEnergySource.lean](CountedEnergySource.lean) and its cost consequences in [CountedEnergyCostSource.lean](CountedEnergyCostSource.lean). The source builds succeeded in manual [CI 42122986713](https://github.com/FlareZ123/bb6/actions/runs/42122986713) and [CI 42123746362](https://github.com/FlareZ123/bb6/actions/runs/42123746362), respectively; every terminal `#print axioms` shows only `propext, Classical.choice, Quot.sound` (or subsets). No replacement model, `sorry`, or `native_decide`.

For **all** `n>=14` and genuine source `CountCone (14*2^n-2*n-16) 3 b d m z`, with no wall and no cost cap, the source theorem gives

```
2^m*(b+12) <= (16*2^n)*(8*2^n*2^n)^z,
m <= n+1+(2*n+3)*z.
```

Thus high-cost histories with `m>=2^n` require `2^n<=n+1+(2*n+3)*z`. The n=62 numerical specialization is kernel-certified as **`z>=36,312,488,334,073,921`**. This improves the older [StrongEnergy.md](StrongEnergy.md) paper bound on the additive constant by exploiting `b+12>=8`; the exact bound is stronger than `m<=n+3+z*(2*n+3)`. This still does not bound z absolutely and does not prove P1 nonhalting. The current source-verified P1 affine wall restriction `3*2^z<=2*(m+n+3)` under `m<=n+z` is independently checked in [CI 42121823464](https://github.com/FlareZ123/bb6/actions/runs/42121823464). All material remains intermediate pending mathematical novelty and full-root impact review.

## Original-source kernel verification: 2026-11-05 22:29 UTC

The exact counted last-positive-reset decomposition and cost bound now pass original-source Lean CI [42120115832](https://github.com/FlareZ123/bb6/actions/runs/42120115832), with standard axioms only. Stronger source theorems also pass [CI 42121823464](https://github.com/FlareZ123/bb6/actions/runs/42121823464):

- [LastResetStrengthSource.lean](LastResetStrengthSource.lean): source-connected outgoing left mass bound `3*2^n <= k+4` for a final positive reset of a candidate with cost `m<=n+z`.
- [CountedWallStrongGateSource.lean](CountedWallStrongGateSource.lean): **unconditional original-source theorem** `BB6.Agent43WallStrongGate.source_wall_near_cost_has_reset_bound` proving `3*2^z <= 2*(m+n+3)` for any genuine counted affine-wall history with `n>=14`, `z>=1`, and `m<=n+z`. The proof preserves the witnessed exact counter and handles arbitrary zero-depth suffixes.
- [WallAboveNPlusZ148.md](WallAboveNPlusZ148.md): new **paper-level** universal numeric inequality combines this original-source theorem with Agent50's already original-source-verified count lower bound to derive `m>n+z` for **n>=148**. The final numeric lemma and composite theorem are **not yet Lean-certified**. Earlier 194 bound is superseded at the paper level.

These are genuine mathematical restrictions on a P1 inverse feeder, not a halt/nonhalt verdict for the machine. Keep in `im-results/` pending source-level composition of the n148 theorem, novelty review and substantial relevance assessment.

## Later stronger results and current strongest frontier

The coarse envelope in this original note has since been sharpened, and a different last-reset method now gives the strongest new information. All new composites are **paper-level**, awaiting a combined unchanged-source Lean CI and novelty review:

- [**LastResetTradeoff.md**](LastResetTradeoff.md): for every original critical counted wall history with `n≥14`, `z≥1`, `m≤2^n`, the exact necessary all-count inequality `2^(n+2*z)≤2^m*(m+n+3)`.
- [**WallAboveNPlusZ.md**](WallAboveNPlusZ.md): combining the last-reset bound with Agent50's previously original-source-Lean-certified `2^n≤24^z*(n+2)^(2*z+2)` proves by an all-n dyadic-shell inequality that every wall history with `n≥194` has `m>n+z`.
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
