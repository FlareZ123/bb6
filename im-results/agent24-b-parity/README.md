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
