# Machine B: aperiodic unsampled parity itinerary (Agent 24)

**Status:** intermediate structural theorem, not a BB(6) holdout decision. Verified with local Lean 4.36.0-rc2 on 2026-11-02; independent CI import from upstream is **not** claimed for this file. The proof copies Agent 18's already source-bridged scalar map and iterator exactly, so the semantic link to the original six-state machine depends on that separate upstream import audit.

## Exact dynamics

Agent 18's two-branch map is

```
G(z) = 3 * floor(z/2) + 4 + 5 * (z mod 2)
iterG 0 z = z
iterG (n+1) z = iterG n (G z)
```

Write `z_n = iterG n 0`, `v_n=z_n+8`, `b_n=v_n mod 2=z_n mod 2`. The Lean-proved affine conjugacy gives

```
2*v_(n+1) = 3*v_n + 7*b_n,       v_0=8.
```

The sequence `v_n` is strictly increasing.

## Main theorem

```lean
iterG_not_eventually_periodic (N k : Nat) (hk : 0 < k) :
  ¬ (∀ n : Nat, (iterG (N+n+k) 0)%2 = (iterG (N+n) 0)%2)
```

**Proof.** If the bits repeated with positive period `k` from time `N`, let `d_n=v_(N+n+k)-v_(N+n)`. Strict monotonicity yields `d_0>0`. Equality of corresponding parity bits cancels the affine correction, giving `2*d_(n+1)=3*d_n` for every `n`. Thus `2^n*d_n=3^n*d_0`. As `2^n` and `3^n` are coprime, `2^n` divides `d_0` for every `n`. Taking `n=d_0` contradicts `d_0<2^d_0`. The Lean code proves every implication for unbounded natural indices without simulation, axioms, or arithmetic black boxes.

**Corollary:** For every cutoff `N`, there exist indices at least `N` with an even `z_n` and with an odd `z_n` (`both_parities_after`). In fact, there is at least one adjacent parity flip after every cutoff.

**Additional exact congruence:**

```
(z_n + 8) mod 7 = (8 * 5^n) mod 7.
```

This follows because `2*v_(n+1) = 3*v_n (mod 7)` and `2*5=3 (mod 7)`. Fully certified by `iterG_mod7`.

## Verification and scope

- Source: [BParityAperiodic.lean](./BParityAperiodic.lean). Execute `lean BParityAperiodic.lean` using supplied Lean 4.36.0-rc2; the file imports only `Lean.Elab.Tactic.Omega`.
- Local axiom audit: `iterG_not_eventually_periodic` and `iterG_mod7` use `[propext, Quot.sound]`; `both_parities_after` uses `[propext, Classical.choice, Quot.sound]`. No `sorryAx`.
- The exact G definition is copied from [Agent 18's BOneDim.lean](../agent18-b-cycle/BOneDim.lean), whose original-machine semantic composition passed pinned-upstream [CI 41393439663](https://github.com/FlareZ123/bb6/actions/runs/41393439663).
- The crucial blank-tape halting question remains whether **one of the extremely sparse recursively sampled values** `iterG (scalarA n) 0` is even. The current theorem explicitly concerns all indices and therefore does not settle the samples. It only rules out eventually periodic full parity itineraries, which obstructs naive fixed-modulus periodic representations of the parity trace.
- This is an elementary but reusable structural result. It is stored under `im-results/`, not promoted to publishable `results/`.

## Next possibilities

Investigate the induced sample-index recurrence and whether a stronger nonperiodicity proof applies to those sampled bits or yields a modulus-free obstruction. Avoid confusing the easily proved existence of infinitely many even **unsampled** iterates with a sampled halting witness.

## Universal parity-prefix separation

The separately compiled [BParityCoding.lean](./BParityCoding.lean) strengthens the aperiodicity analysis into a **finite** and **all-starts** theorem. Let \(T(v)=(3v+7(v\bmod2))/2\), and \(T^i(v)\) denote its \(i\)-th iterate. For any natural \(a\le b\), agreement of the first \(n\) parity bits proves

```lean
prefix_forces_divisor (a b n : Nat) (hab : a ≤ b)
  (hp : ∀ i, i < n → (path a i)%2 = (path b i)%2) :
  2^n ∣ b-a
```

Consequently, whenever \(a<b\) and \(b-a<2^n\), there is a parity disagreement at some \(i<n\) (`finite_prefix_separates`). The proof propagates the ordered difference while parity matches and uses coprimality of \(2^n\) and \(3^n\); there is no infinite-tail assumption. This gives a quantitative finite-prefix injectivity certificate and a candidate building block for two-adic coding of the reset sampler.

Compiled locally under Lean 4.36.0-rc2 with axiom audit `[propext, Quot.sound]`, no `sorryAx`. This is an intermediate statement about the exact scalar map; it still does not decide recursively sampled parity.

## Sharpened exact coding theorem (06:37 UTC)

The Lean proof has since been strengthened to a **biconditional**: for all naturals `a≤b`, the first `n` bits in their `T` itineraries agree **if and only if** `2^n ∣ (b-a)`. The forward implication is `prefix_forces_divisor`; the converse is `divisor_forces_prefix`; `prefix_iff_congruent` composes them.

Thus the length-`n` binary parity prefix identifies the starting integer's residue class modulo `2^n` exactly. The all-time theorem `full_itinerary_injective` proves that two different natural starting states cannot have identical parity itineraries forever. All four theorems compile with only `[propext, Quot.sound]` under Lean 4.36.0-rc2. These are strong source-independent parity-coding facts, but remain classical-style structural statements about the copied scalar map, and do not solve the sampled-index halting condition.

## Exact finite parity-word synthesis and prior art (06:48 UTC)

The new `inputFor` algorithm builds the unique integer \(a<2^n\) whose first \(n\) parity bits equal an arbitrary prescribed word \(b_0,\ldots,b_{n-1}\). It starts at zero and, at bit position \(i\), adds \(2^i\) exactly if the current \(i\)-th output bit disagrees with \(b_i\). The key universal lemma is

```
path_shift_pow: T^[n](a+2^n*t)=T^[n](a)+3^n*t
```

and the special case `parity_bit_lift` that adding \(2^n\) preserves output bits before time \(n\) and toggles the bit at time \(n\). All of these are proved in [BParityCoding.lean](./BParityCoding.lean), including `inputFor_lt`, `inputFor_prefix`, and `inputFor_unique`, with `#print axioms` showing only `[propext, Quot.sound]`.

**Prior art correction:** The existence and bijectivity of such parity codings for generalized \(3x+k\) maps is classical, and must **not** be portrayed as a novel publishable BB(6) discovery. Bernstein and Lagarias, *The 3x+1 Conjugacy Map* (Canadian Journal of Mathematics 48, 1996), https://websites.umich.edu/~lagarias/doc/bernstein.pdf , explicitly discuss the general odd \(ax+b\) case and the 2-adic shift conjugacy. Our shifted map is exactly \(T(v)=(3v+7(v\bmod2))/2\), an instance of this known theory. The deliverable here is a precise **Lean-checked specialization integrated with Agent 18's exact Machine B counter map**, plus a particular aperiodicity and modular relation for the blank-entry scalar orbit. The dynamically sampled return indices remain the central unknown; the classical parity-coding bijection alone gives no holdout decision.

## Structural restriction on the actual recursively sampled resets

[BResetResidues.lean](./BResetResidues.lean) imports the local Lean-certified exact `iterG` model and copies Agent 18's `scalarA` recursion as `resetA`:

```
A[0]=3, Z[n]=iterG A[n] 0, A[n+1]=Z[n]+9-3*(Z[n]%2).
```

Unlike the unsampled parity coding above, the following statements constrain **every recursively induced reset index**, for every natural cycle number (including the syntactic continuation after a possible halt):

- `resetA n % 6 ∈ {1,3}` for all `n`. The proof uses `G(z)%3 ∈ {0,1}` for every input and oddness of each reset.
- `(Z[n]+8)%7 ∈ {5,6}`, using the exact `(iterG m 0+8)%7=(8*5^m)%7` and the previous modulo-six restriction.
- **Survival/halting index residue dichotomy:** `Z[n]%2=1 ↔ A[n+1]%7 ∈ {3,4}`; `Z[n]%2=0 ↔ A[n+1]%7 ∈ {0,6}`. The two biconditionals are `sample_odd_iff_reset_residue` and `sample_even_iff_reset_residue`.

All these universal statements compiled locally in Lean 4.36.0-rc2 with only `[propext, Quot.sound]`; no finite bound on `n`. This yields an exact modular **alternative test** for a halting sample, but is currently a rearrangement of the same undecided sampled-parity problem, as the next index itself is defined from that parity. It does **not** imply any halting witness or all-time nonhalting. A direct imported equality between this copied `resetA` and the existing Agent 18 `OneDim.scalarA` is straightforward but is not yet separately CI-certified.

## Quantitative finite-time obstruction to repeating parity (07:02 UTC)

[BParityDiscrepancy.lean](./BParityDiscrepancy.lean) imports the previous two modules and proves an explicit *linear-in-offset* bound strengthening their generic aperiodicity result. For the actual blank-entry shifted scalar orbit \(v_n=G^n(0)+8\), every \(N\ge0\) and positive proposed period \(k\) have a parity disagreement at some \(0\le i<N+k+3\):

```lean
parity_disagrees_linear (N k : Nat) (hk : 0<k) :
  ∃ i : Nat, i<N+k+3 ∧
    orbit (N+i+k)%2 ≠ orbit (N+i)%2
```

Proof: the finite-prefix two-adic injectivity lemma implies that a common parity prefix of length \(m\) forces \(2^m\) to divide \(v_{N+k}-v_N\). The shifted trajectory is strictly increasing, while induction from its exact recurrence gives \(v_j\le 2^{j+3}\). The positive difference is therefore strictly below \(2^{N+k+3}\), so \(m=N+k+3\) matching bits are impossible. It also proves the stronger gap-sensitive lemma `parity_disagrees_within_gap` when a sharper value of the separation is known.

This quantitative nonrepetition theorem compiles locally in Lean 4.36.0-rc2 with only `[propext, Quot.sound]`, no `sorryAx`. It concerns full scalar parity histories; the recursively sampled halting criterion remains unresolved.

## Original-machine source bridge: independently certified (07:03 UTC)

**The complete end-to-end Machine B interpretation is now Lean-kernel-certified against the unmodified pinned original-machine implementation**, not merely inspection of copied maps. Manual upstream workflow [41403230037](https://github.com/FlareZ123/bb6/actions/runs/41403230037) **passed** (2026-11-02 07:01 UTC, commit `fdb1fe977bfef98f37c21d5e73904d0ad791e351`), compiling the unmodified Agent18 `BReduction.lean, BRun.lean, Agent18BBridge.lean, BOneDim.lean, Agent18OneDimBridge.lean`, then Agent24 `BParityAperiodic.lean, BResetResidues.lean, Agent24BResidueBridge.lean`, against Cryptids SHA `ced8f9f44f67a167d5ecc03e687b048c67926371` and the pinned upstream Lean v4.35.0-rc4 toolchain.

```lean
BB6.Agent24.SourceBridge.raw_halts_iff_mod7_reset :
  IsHalt BB6.Bridge.Source.target ↔
    ∃ n : Nat, BB6.Agent24.Reset.resetA (n+1)%7=0 ∨
      BB6.Agent24.Reset.resetA (n+1)%7=6
```

The bridge proves by **definitional equality and induction** that Agent24's scalar `G`, `iterG`, and `resetA` exactly equal Agent18's source-connected `OneDim.G`, `OneDim.iterG`, and `OneDim.scalarA`. Axiom audits:

- `source_G_eq`, `source_iterG_eq`, `source_scalarA_eq`: **zero axioms**.
- `raw_halts_iff_mod7_reset`: **`[propext, Classical.choice, Quot.sound]`**. No `sorryAx`, `admit`, or `native_decide`.

The first CI dispatch [41402790071](https://github.com/FlareZ123/bb6/actions/runs/41402790071) failed only because a module-mode file attempted to import the nonmodule `BResetResidues.lean`; removing the `module` declaration from the bridge resolved this without changing its mathematical content. The successful second run reproduces the complete chain.

**Scope caution:** This is a source-audited *equivalent reformulation* of the same undecided B stopping question. Since `resetA` is computed from the parity sample itself, the modular target `{0,6}` is not a currently verified exclusion. It cannot be promoted to a BB(6) value or to a decision of this holdout.

## Failure of the obvious finite-modulus induction

If all preceding sampled cycles survive, the two proved index restrictions combine to put every subsequent reset index into one of **`{3,25,31,39}` modulo 42**. This condition is necessary but still vastly too weak to prove the sampled parity stays odd.

Two Lean-kernel-checked counterexamples in [BMod42Failures.lean](./BMod42Failures.lean) are:

```lean
generic_residue_31_even : (iterG 31 0)%2=0
generic_residue_45_even : (iterG 45 0)%2=0
```

Both theorems use `by decide` and have **zero axioms**; `31 mod 42=31` and `45 mod 42=3` lie in the candidate survival index classes. These indices are synthetic and **are not known to occur in the true blank-entry reset sequence**. They refute any blanket implication from membership in those four classes to odd sampled parity. A successful nonhalting invariant must exploit *more than these ordinary residue restrictions* and, in particular, features of the recursively selected A_n.

## Concrete obstruction to bounded-bit modular prediction

The `parity_bit_lift` theorem gives a precise negative result for a broad family of proposed shortcuts: for every \(n\) and every starting integer \(a\), the starts \(a\) and \(a+2^n\) agree modulo \(2^n\), yet their parity outcomes at iteration \(n\) are **opposite**. Their first \(n\) parity bits also agree. Consequently, **no predictor using only the starting state modulo \(2^n\) can correctly determine its \(n\)-th output parity for every input**. In this exact sense, to predict the bit at time \(n\) uniformly, the input needs one additional 2-adic digit. This is a theorem about uniform low-bit predictors; it is **not** a computational lower bound on all algorithms for the specific initial value 8, and does not rule out more sophisticated special-value identities or symbolic computation.

Combined with `parity_disagrees_linear`, this points away from a finite fixed-modulus encoding of Machine B's **complete** parity trace. The true unknown is the sparsely sampled sequence. A finite-state invariant only for the reachable reset orbit is still logically possible and would require extra structure.

## Uniform growth envelope for the actually sampled recurrence (07:12 UTC)

The auxiliary source [BSampleEnvelope.lean](./BSampleEnvelope.lean) imports the actual recurrence `resetA` and the translated scalar orbit and proves **unconditional, all-index, two-sided bounds** that hold even after a hypothetical halting sample. With `A=resetA n`, `Z=iterG A 0`, the locally Lean 4.36.0-rc2 verified statements are

```
8*3^A ≤ 2^A*(Z+8)
2^A*(Z+15) ≤ 15*3^A
Z+6 ≤ resetA(n+1) ≤ Z+9.
```

In particular `all_reset_index_growth` proves for **every** natural `n`:

```
8*3^(resetA n) ≤
  2^(resetA n)*(resetA(n+1)+2)

2^(resetA n)*(resetA(n+1)+6) ≤
  15*3^(resetA n)
```

The exponential inequalities come from the exact affine recurrence `2v_{m+1}=3v_m+7(v_m%2)`, `v_0=8`, and hold uniformly without simulation. `#print axioms` for the bounds prints only `[propext, Quot.sound]` in the underlying scalar proof and the standard `Classical.choice` where used by imported theorems; no `sorryAx`. They sharply quantify superlinear reset growth, but are not a parity invariant and do not classify the original six-state machine.
