# BB429: dyadic indistinguishability of blank and synthetic halting starts

**Agent 4, 2026-11-05. Status: intermediate formal mathematical statement.** The original blank-start six-state machine #429 and BB(6) remain unresolved. The constructed halting starts in this note are **synthetic accelerated inputs**, and none is asserted to be reached by the actual blank-tape orbit.

## Mathematical theorem

Let `BB429.next` be the exact twelve-branch, two-counter high-level map in the repository's unchanged `im-results/agent5-429-rank/BB429Rank.lean`. Its actual accelerated blank seed is `(0,0)`, and its unique macro halting line is `w+1=2*u`.

For any natural modulus exponent `k`, define
```text
d(0)   = 17
d(k+1) = 4*d(k) + 13
W(k)   = 12*2^(d(k)) - 3*d(k) - 13.
```
Then:

1. **Divisibility:** `2^k | W(k)`, so the synthetic seed `(0,W(k))` and the actual seed `(0,0)` have *identical residues in both counters modulo `2^k`*.
2. **Actual halting in the complete accelerated map:** there exist naturals `n,a,b` with `BB429.run n (0,W(k))=some(a,b)` and `BB429.next(a,b)=none`.
3. **Universal obstruction:** For every predicate `P : Nat × Nat → Prop`, the conjunction of (i) `P(0,0)`, (ii) `P` is saturated under same-two-counter residues modulo `2^k`, (iii) `P` is preserved by every successful `BB429.next` step, and (iv) no `P` state is halting, is logically impossible.

This rules out **every sound, blank-containing forward inductive invariant expressible solely in the two counter residues modulo one fixed power of two** as a complete nonhalting proof for this high-level machine. It does not rule out non-periodic invariants, richer phase variables, exact blank ancestry conditions, or properties restricted to other legitimate subsections.

## Proof mechanism

The previously source-verified Agent5 first-burst classification `BB429Burst.burst_gateway_iff` gives the exact necessary-and-sufficient halting-gateway equation for a first-only prefix from `(u,w)`:
```text
2*u+w+3*n+13 = 4*(u+3)*2^n.
```
For `u=0` and `w=W(k)`, this identity holds at `n=d(k)`. The new `first_prefix_is_source` formally embeds every successful first-only macro prefix into the **complete** `BB429.run`, and the unchanged `BB429.next_none_iff_halt_line` converts the gateway to the actual `none` result. Independently,
```text
3*d(k)+13 = 64*4^k,
```
which, combined with `d(k)≥k`, yields `2^k | W(k)`. Finally, forward induction carries any proposed residue-saturated invariant along the genuine halting synthetic trace, contradicting its halting exclusion.

Source: [BB429DyadicStarts.lean](BB429DyadicStarts.lean). The final named Lean theorem is `BB429DyadicStarts.no_dyadic_halt_separating_invariant`. It imports the two original Agent5 modules and uses no arbitrary time cutoff. Agent5's finite-burst theorem is **prior work**; the new formulation records a method limitation, not a new blank-root decision.

## Verification and priority

The new Lean module compiled locally under Lean 4.36.0-rc2 against a **temporary declaration-only interface** faithfully matching the actual previously kernel-verified imported theorem statements. The local proof itself has no `sorryAx`, but the temporary interface contained two `axiom` declarations standing in for pre-existing real theorems. This is a preliminary check. The intended stronger verification is a manual repository CI compilation with the **unaltered original** `BB429Rank.lean` and `BB429Burst.lean`, including the complete axiom audit; status will be updated after that run. The temporary interface was not committed.

The scientific lesson is to avoid investing in ever-finer, *purely dyadic two-counter finite-state forward quotients* as a prospective complete proof. Modulo-2^k filters remain valuable as necessary reachable-state conditions and may combine with stronger non-periodic arguments. No particular surviving halting residue class has been proved genuinely reachable from blank, and no original-machine halt or nonhalt decision follows.


## Stronger theorem: **every** dyadic counter cylinder contains a halting synthetic input

The later [BB429EveryDyadicClass.lean](BB429EveryDyadicClass.lean) strengthens the construction above from the single congruence class of blank to **arbitrary** `k,u,w : Nat`:

```lean
∃ W n a b, W % (2^k) = w % (2^k) ∧
  BB429.run n (u,W) = some (a,b) ∧
  BB429.next (a,b) = none
```

The first counter of the synthetic input is exactly `u`; in particular **every one of the `2^(2k)` classes of complete two-counter residue pairs modulo `2^k` contains a halting accelerated input.** A second universally quantified theorem `no_nonempty_dyadic_haltfree_invariant` says this prevents any **nonempty** same-residue-saturated forward inductive invariant of the complete map from excluding all halting configurations. No special status is assigned to the blank class in this stronger statement.

The constructive arithmetic is elementary and parameter-uniform. Define
```text
G(0)   = 0
G(k+1) = 4*G(k)+1
C      = 2*u+w+13
n      = C*G(k)+(C+k+1)*4^k
W      = 4*(u+3)*2^n-(2*u+3*n+13).
```
The key identities are `3G(k)+1=4^k`, `3n+C=(4C+3k+3)*4^k`, and `n≥C+k+1`, making `W` a well-defined natural with `W≥w`. Thus both `W-w` and the first-branch terminal equation are certified for all parameters: `2^k | (W-w)` and `2u+W+3n+13=4(u+3)2^n`. The imported Agent5 exact first-burst criterion yields the corresponding *real* full-map synthetic halt. The first-branch theorem and source map remain prior work.

A superficial modular obstruction that can exclude selected *halting gateways on the genuine blank orbit* may still be valuable because it uses extra root-specific information; the theorem applies only to a single global invariant for **all possible input states in the same full residue cylinder**. It does not preclude stronger abstractions that remember reset histories or additional nonperiodic state.

The full stronger module independently compiled locally under Lean 4.36.0-rc2 against the same two previously source-verified theorem signatures (no new `sorry`). The manual source audit workflow was extended to compile both modules against unchanged checked-in Agent5 sources; dispatch [41969085136](https://github.com/FlareZ123/bb6/actions/runs/41969085136) is pending as of 04:40 UTC. The preliminary one-module run [41968466747](https://github.com/FlareZ123/bb6/actions/runs/41968466747) is also pending. This is a method-limitation theorem, not a BB(6) bound or an actual halting or nonhalting decision.
