# Agent 28: scalar normal form and a uniform low-cost P1 even-exit obstruction

**2026-11-03. Intermediate source-aligned result, not a P1 or BB(6) decision.** Research pilot: [R-20261103T1513Z-agent28-p1-word-automaton](../../research/issues/R-20261103T1513Z-agent28-p1-word-automaton.md). The critical limitation is that the final theorem has been verified **locally as pure Lean arithmetic under the exact two source-proved inverse equations**, but its composition with all unmodified upstream repository modules has **not** yet been run through original-source CI. The shared GitHub Actions runner outage on Nov. 3 precludes a clean source-audited integration claim.

## Full original-source Lean certification (Agent 45 audit, 2026-11-03)

**The source-integration uncertainty documented further below has been resolved.** Original Agent 28 mathematical source `P1Scalar.lean.xz.b64` and the existing original source-bridge `P1ScalarBridge.lean.xz.b64` were decoded without alteration. A SHA-256 check verified the mathematical file as `56fc4dbfb187bcb54302d04580cb138556fa7eb110d1f263ffd25bdc5f3b23d4`. The manual-only verification workflow [`agent45-p1-scalar-source.yml`](../../.github/workflows/agent45-p1-scalar-source.yml) compiled unmodified source `GParity.lean`, `GInverse.lean`, `PosEvenForm.lean`, `P1FiniteInverse.lean`, `P1InverseLog.lean`, `MassInverse.lean`, `OddConeMass.lean`, and `InverseIff.lean` before the decoded original Agent28 modules.

**Successful full-source run:** [41726473172](https://github.com/FlareZ123/bb6/actions/runs/41726473172), source SHA `3980941e60e525badc1739f00099bb28b2ded5ad`, job `126232447207` **success**. Final `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for `BB6.Agent28Scalar.source_critical_low_cost_even_exit` and `source_odd_inverse_normal_form`, and `[propext, Quot.sound]` for `source_critical_cone_hub`. There were no Lean errors, no `sorryAx` and no mock replacements. The mathematical theorem and ready-made source bridge are **credited to Agent 28**; this run provides the missing direct original-source audit.

The new source-connected theorem states: for **every** natural critical exponent `n≥4`, every genuine `BB6.Agent1Quarter.OddCone (14*2^n-2*n-16) 3 b d m`, every actual `inverseAt b d t=some(k,c)` with `b≥8`, `b%4=0`, `k≥2`, **positive even** `c≥2`, cumulative `m≤2^n`, and genuine blank-origin `BB6.Agent1.Reach (2*k-4) (c+4)`, one must have **`t=1 ∧ b=4*(m+n)`**. This is a universal necessary low-cost terminal restriction, particularly relevant to the unsolved `n≡14 (mod16)` branch. It does **not** bound total inverse cost, preclude wall membership, resolve exceptional `c=1`, or decide P1 or BB(6).

## Main quantified arithmetic result

Let `n >= 4`, `X=2^n`, and `K=7*X-n-3`. For a synthetic odd-sector inverse hub `(b,d)` at cumulative inverse cost `m`, introduce a normalized right coordinate `D` with

```text
b + 2*(D+m) + 8 = 2*K,      d = 2*D + 1.
```

The genuine P1 critical precursor `(14*2^n-2*n-16,3)` corresponds to `(D,m)=(1,0)`; Agent 1's source-proved OddCone mass conservation guarantees this balance on any authentic odd-predecessor chain.

Use the source-proved exact complete inverse equations for `inverseAt b d t = some(k,c)` with odd d, b divisible by four, and b >= 4 (Agent1 `InverseIff.lean`):

```text
d+b/2+3 = 2^t*(c+3),
2*k+c+2*t+1+c%2 = b+d.
```

If an **even positive input** `c>=2` has `c%2=0`, and its even-left feeder satisfies the genuine blank-reachability necessary power equation `2*k+8=14*2^j`, then, **provided `m<=2^n`, `b>=8`, `b%4=0`**, the locally Lean-proved theorem `BB6.Agent28Scalar.critical_low_cost_even_dichotomy` establishes universally:

```text
t=1,        j+1=n,        b=4*(m+n).
```

This is a clean, **all-parameter** low-cost bottleneck for the n≡14 (mod16) sector, though its statement holds for any n>=4 under the displayed exact equations. It removes every positive-even exit at depth >=2 below the exponential cost threshold and constrains depth-one exits to one affine wall. It does **not** assert that such a wall is actually reachable, and gives **no result for m>2^n** or for exceptional input c=1.

Proof architecture: for t>=2 the shifted equation forces `4*(c+3)<=d+b/2+3`, and exact depth t cannot exceed n+1 because `2^t*(c+3)<14*2^n` and c>=2. The new arithmetic proof shows `7*2^n<2*k+8<14*2^n`, a gap containing no fourteen-power. At t=1, exact elimination yields `2*k+8+n+m=7*2^n+b/4`. With m<=2^n this gives a strict quarter-window `14*2^n <4*(2*k+8)` and `2*k+8<14*2^n`; power index j must satisfy j+1=n and then `b=4*(m+n)`.

## Exact scalar odd-inverse grammar

For an odd source input `c`, set `l=t+1`, `D'=(c+3)/2` and `m'=m+l`. Then the true inverse equations are **equivalent** to

```text
2^l * D' + m = K+D,
(2*k-4) + 2*(D'+m') + 8 = 2*K.
```

Consequently, the next odd hub is specified by just `D'=(K+D-m)/2^l` and `m'=m+l`, with the exact divisibility condition, `D'>=3`, and positive-left eligibility. Its source-required left-divisible-by-four condition is exactly `(D'+m')%2=K%2`. For even n, K is odd; the parity test depends only on the parity of the quotient and cumulative inverse cost. This is an explicit quotient-state repackaging of Agent1's previously certified mass/shift coordinates, not a claim of discovering a separate dynamical system.

The unique even-input terminal of any node with shifted `s=K+D-m` and odd part `U=s/2^v`, `v=v2(s)`, has candidate `2*k+8=2*K-2*m-U-2*v+3` if `U>=5`; exceptional c=1 appears only when `U=1`. These are exact arithmetic identities, and the formal low-cost theorem addresses all positive-even depths without relying on enumerating any finite cone.

## Formal Lean certificate and trust boundary

- [P1Scalar.lean.xz.b64](./P1Scalar.lean.xz.b64): original standalone Lean 4.36.0-rc2 source, XZ-compressed then base64-encoded. Unpacked UTF-8 SHA-256: `56fc4dbfb187bcb54302d04580cb138556fa7eb110d1f263ffd25bdc5f3b23d4`.
- Successfully compiled locally with `Lean 4.36.0-rc2`, `import Std`, *no sorry, no axioms added, no unsafe*. `#print axioms` for the key `critical_low_cost_even_dichotomy` is exactly `[propext, Classical.choice, Quot.sound]`. Separate `odd_inverse_normal_form` requires `[propext, Quot.sound]`.
- This is a mathematically complete Lean theorem *about the source equations supplied as hypotheses*. The cited upstream `BB6.Agent1Quarter.inverseAt_iff_power_mass`, Agent1 `OddConeMass` and `BB6.Agent1.even_left_power_shape` are separately source-certified in prior CI, but their composition with this new theorem and source provenance must still be built and audited under the original repository imports. Do not misreport this as the final source-connected Reach theorem.
- The theorem is a necessary constraint on **synthetic** inverse histories. Blank-reachability and absence of all other routes require separate proofs. The exact BB(6) value is unknown.

## Independent bounded arithmetic stress tests

[dual_check.py.xz.b64](./dual_check.py.xz.b64) stores two independently implemented exact-integer traversals in one self-contained Python file: one follows the upstream recursive `inverseAt` formulas directly, while the other follows the normalized dyadic quotient graph. Unpacked SHA-256: `4193939bab92e6496aebb61bf8346c9daebfb7077f9252a44462ae605e1e20fd`.

Both traversals agree **exactly** on every count and maximum inverse cost for the 64 fixed integers `n=14+16*q`, `0<=q<64` (i.e. n<1024), with a cap of 200,000 unique odd hubs per n and no cap reached. Every tested finite tree exhausts with no exceptional c=1, no power match and no unclassified positive predecessor. Across the 64 fixed n there were **192,480** odd hubs; the largest tree is n=286 with **155,987** hubs and maximum m=1,440, followed by n=350 with 15,943 hubs and n=750 with 11,707. These are **computational certificates of bounded finite samples under the source-derived necessary conditions**, not kernel-certified unreachability theorems, and do not imply a uniform conclusion for any infinite n family. Differential result JSON SHA-256: `5deab159029635107990aad2978bea8fe4ec29b0638de26f1d71f91b8cbc287d`.

An independent conservative affine-family engine tested n=1024*q+r, including r=30,286,526,750 (all outside the previously closed 36 residue classes). Splitting q into all classes modulo 2^h for h<=4 left every subfamily unresolved because of a nonuniform left-coordinate parity branch, despite the finite q=0 examples closing. This is a failure of that fixed-affine proof technique, never evidence of true reachability.

## Prior work, falsifiers and next target

Agent28's original 36 affine residue families and Agent47's source-certified r=14/62 exclusions predate this investigation; Agent33's source-certified unbounded upper-chain theorem and Agent1/Agent9's original mass/exponential-wall reductions also predate it. This new low-cost wall should be independently compared with Agent9's n=16q+2 dichotomy before any originality/publication claim.

A genuine P1 n≡14 all-parameter exclusion would need either (1) a **uniform bound** `m<=2^n` for all relevant odd-inverse histories plus exclusion of all wall nodes `b=4*(m+n)`, or (2) a new obstruction for high-cost histories, and separately the exceptional input c=1. Even a wall exclusion alone would be insufficient without the high-cost and exceptional cases.

The first source-integration action when CI recovers is to import the unpacked module alongside original `InverseIff.lean`, compose `odd_inverse_normal_form` with `inverseAt_iff_power_mass`, compose `critical_low_cost_even_dichotomy` with original `odd_cone_mass` and `even_left_power_shape`, and audit the final theorem and axioms on unmodified dependencies. The current source-independent Lean kernel check is reproducible without CI.

## 2026-11-04: all-depth source-certified odd-word cost bound

**New source-connected Lean theorem; P1 and BB(6) remain open.** The original `OddConeMass` and `InverseIff` modules, together with the new [OddWordCost.lean](OddWordCost.lean) and [OddWordSourceBridge.lean](OddWordSourceBridge.lean), compiled successfully on the unchanged repository sources under Lean 4.36.0-rc2 in [manual/one-shot CI run 41744759255](https://github.com/FlareZ123/bb6/actions/runs/41744759255) (job 126294854122, success). Before CI, the same bridge was compiled against mock signatures matching the two source theorem interfaces. The source CI eliminates that substitution risk for the original two bridge theorems. The further `source_critical_wall_cost_logarithmic_gap` convenience corollary was added **after** this CI and is not yet source-run audited.

The essential new abstraction is the exact odd-inverse word recurrence `2^l*D' + m = K+D`, `m'=m+l`, `l=t+1≥1`. For any finite word of costs `l_i`, define prefix costs `m_0=0, m_{i+1}=m_i+l_i`, and coefficients `A=Σ_i 2^(m_i)` and `T=Σ_i m_i*2^(m_i)`. The pure kernel-proved invariants are `2^m D+T=1+K*A` and `A<2^m`. These are **all-word** identities rather than bounded-depth modular samples.

At a hypothetical affine wall `b=4(m+n)`, the genuine source-normalized coordinates give `D+3m+2n+4=K` with `K+n+3=7*2^n`. The universal Lean theorem `source_oddcone_wall_cost_logarithmic_gap` consequently proves

```
2^(n-m) < n,      for every n≥14 and every finite OddCone on the wall.
```

Thus, when `m<n`, `m > n-log₂(n)`, and in particular `2m≥n`. This is an exact *necessary* cost threshold for a synthetic source inverse wall, independent of reset count. It does **not** prove the wall unreachable or constrain the exceptional `c=1` and high-cost even exits. Compare Agent9's already source-certified near-logarithmic cost bounds for the distinct `n≡2 mod16` feeder program before asserting originality.

A separate [ONE-RESET-WALL.md](ONE-RESET-WALL.md) derives a stronger exclusion for **zero/one positive-depth inverse transitions** when `n≡14 mod16`, including the n14 exception and all n≥30. Its general numerical contradiction and dyadic lemma are kernel checked in [OneResetCore.lean](OneResetCore.lean), [OneResetGrowth.lean](OneResetGrowth.lean), and [OneResetTwoAdic.lean](OneResetTwoAdic.lean); the normalized-word-to-source bridge for the *one-reset shape* remains to be formalized and independently reviewed. Do not report the one-reset statement as source-certified yet. Review requested from Agent45 in `communications/agent45/2026-11-03T2357Z_agent28-one-reset-source-review.md`.


## Original-source verified n≥30 one-reset wall exclusion (2026-11-04)

**New source proof:** the unchanged upstream P1 `inverseAt`, `OddCone`, `UpperTail`, and exact inverse equations, together with Agent28's new arithmetic modules, compiled in [manual opt-in CI 41747017916](https://github.com/FlareZ123/bb6/actions/runs/41747017916), job 126302477410 **success**, using Lean 4.36.0-rc2. The final theorem is `BB6.Agent28.source_critical_one_reset_no_wall` in [OneResetSourceBridge.lean](OneResetSourceBridge.lean). Local proof checks and CI have no `sorry`, and the local final axiom audit contains only `[propext, Classical.choice, Quot.sound]`; no mock dependency was used in this successful CI.

For every natural **n≥30**, consider the genuine critical inverse cone from `(14*2^n−2n−16,3)`, an arbitrary original `UpperTail` from this root, one exact `inverseAt` step of positive depth `t≥1` producing an odd-right predecessor, and another arbitrary original `UpperTail`. If the final state is in the genuine `OddCone`, the affine wall `b=4(m+n)` is **impossible**. This includes every exponent n=16q+14 with q≥1, and applies to many other exponents at the equation level.

Proof modules: [OneResetGrowth.lean](OneResetGrowth.lean), [OneResetTwoAdic.lean](OneResetTwoAdic.lean), [OneResetBudget.lean](OneResetBudget.lean), [OneResetSourceEq.lean](OneResetSourceEq.lean), [OneResetPoly.lean](OneResetPoly.lean), [OneResetSourceBudget.lean](OneResetSourceBudget.lean), [OneResetSourceBridge.lean](OneResetSourceBridge.lean). The first expanded CI 41746777745 found one missing import in `OneResetSourceBudget.lean`; it was fixed at d14efc4c, followed by the successful full-source re-audit. The proof mechanism is detailed in [ONE-RESET-WALL.md](ONE-RESET-WALL.md). Its finite n=14 case is a separate arithmetic enumeration and is not part of this source theorem.

A stronger count-annotated consequence `source_critical_wall_needs_two_resets` is implemented in [OneResetZero.lean](OneResetZero.lean) and [OneResetCount.lean](OneResetCount.lean), which locally compile against exact-matching mock source signatures. **The full counted theorem is now original-source certified**: [manual opt-in CI 41747347637](https://github.com/FlareZ123/bb6/actions/runs/41747347637), job 126303562909, completed **success** on unchanged upstream `OddCone`, `inverseAt`, and `UpperTail` source under Lean 4.36.0-rc2. The final theorem `BB6.Agent28.source_critical_wall_needs_two_resets` proves that every genuine `OddCone (14*2^n-2*n-16) 3` wall history, for every n≥30, admits a *faithful exact positive-depth edge count z≥2*. Zero-reset and one-reset cases are both ruled out. The Lean proof source contains no `sorry` or user-created axioms. It does not preclude histories with z≥2 or any P1 halt gate outside this affine wall. The general multi-reset continuation is [MULTIRESET-DEFECT.md](MULTIRESET-DEFECT.md), with the locally Lean-proved arbitrary reset algebra [DefectTransport.lean](DefectTransport.lean).

Even after this advance, P1 and BB(6) remain open: two or more resets, high inverse cost, the exceptional c=1 route, other exponents, and genuine blank-orbit reachability require separate work. The present exclusion is an intermediate mathematically exact result whose external academic novelty has not yet been independently assessed.

