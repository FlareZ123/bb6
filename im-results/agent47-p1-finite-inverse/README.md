# Agent 47: exact finite inversion and critical-index valuation for P1

Status: new **source-level, standard-axiom Lean theorems** about the published accelerated P1 system, with original semantic dependency from Agent 1. No claim to have resolved P1 halting or BB(6), and no publishable global result is asserted here.

## Root source and verified dependency

The P1 holdout is `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`. Agent 1 formalized the exact recursive drain `G` and the complete inductive inverse relation `BB6.P1Reduction.GAncestor` in `im-results/agent1-p1-map/GInverse.lean`. Agent 50 proved a blank-reachable positive-output hub must have a predecessor through `GAncestor` unless a special input `c=1` is possible, in `im-results/agent50-p1-residue/P1ResidualReach.lean`. Agent 19 independently source-bridged the accelerated machine to the raw six-state machine. We **import those unmodified sources** and prove the new claims below. They are statements about the original P1 map, without invented transition assumptions.

A manually dispatched, source-level Lean 4.36.0-rc2 workflow `.github/workflows/agent47-p1-finite-inverse.yml` checks the complete dependency chain. Prior passing runs: [finite inverse 41424509713](https://github.com/FlareZ123/bb6/actions/runs/41424509713), [blank-reachability bridge 41424706211](https://github.com/FlareZ123/bb6/actions/runs/41424706211), [all-critical-index exceptional-one exclusion 41425031997](https://github.com/FlareZ123/bb6/actions/runs/41425031997), [all-index 2-adic valuation 41425459311](https://github.com/FlareZ123/bb6/actions/runs/41425459311). Source-level audits print exactly `[propext, Quot.sound]` on our core theorems, no `sorryAx` or `unsafe`.

## Exact inversion without recurrence or unbounded search

`P1FiniteInverse.lean` defines a total executable `inverseAt b d t` returning the unique predecessor pair at inverse depth `t`, when it exists. On the upper step, `(b,d)` has parameters `k=b/4-1`, `c=d+b/2`; on a nest step `c` is replaced by `(c-3)/2` and `k` by `k+c'/2+1`, if the old counter is odd and at least three. Theorems:

* `inverseAt_sound`: every computed pair is a genuine `GAncestor`.
* `inverseAt_complete`: every genuine pair occurs at some depth `t` with `c+t<=d+b/2`.
* `ancestor_exists_iff_power`: for `4<=b`, `b%4=0`, a predecessor with right counter `c` exists iff `d+b/2+3=2^t*(c+3)` for some natural `t`.
* `exceptional_one_iff_power`: a forbidden exceptional source right-counter `c=1` occurs iff the shifted output `d+b/2+3` equals `4*2^t` for some `t`.
* `inverse_iff_mem`: an ancestor pair occurs iff it belongs to the executable `inverseList b d`, a finite `List.filterMap` over a known integer range.

This gives a reusable, kernel-sound finite enumeration interface for automatically producing inversion proof certificates. Completeness is mathematically quantified over **all** natural predecessor states; it is not a finite simulation horizon.

`P1ConeListBridge.lean`: theorem `no_reach_of_inverse_list` transfers all-time unreachability of every member of a hub's finite predecessor list to actual blank-entry non-reachability of the hub, provided that `c=1` has been excluded by the exact arithmetic power test. It directly invokes Agent 50's source-level `positive_G_feeder`. This can underpin a kernel-checked finite cone checker and avoid handwritten per-residue ancestor proofs. **It does not itself certify the 5,264 candidate affine cones identified by Agent 4; further parametric inequality and recursion certificates are needed.**

## All-index critical-target structure

The actual P1 halting gateways have critical counter `H(n)=14*2^n-2*n-10`. Agent 50's source theorem `critical_target_implies_three` reduces hypothetical blank reachability of `(2,H(n))` to the hub `(H(n)-6,3)`. For every `n>=4`:

1. `P1NoRootOne.lean`, theorem `critical_hub_no_one`: no `GAncestor (H(n)-6) 3 k 1` exists, for **any** k. Proof is a strict gap between adjacent powers: the shifted output `7*2^n-n-2` lies between `4*2^n` and `8*2^n`, and can never be `4*2^t`.
2. `P1CriticalValuation.lean`, theorem `critical_hub_shift_all_powers`: for all natural exponents `t`,
   ```
   (2^t ∣ 3 + (14*2^n-2*n-16)/2 + 3) ↔ (2^t ∣ n+2).
   ```
   The enormous counter's **entire 2-adic divisibility profile** equals that of the small integer `n+2`. The proof works for `t<=n`, and excludes all higher exponents by a strict magnitude argument. Unlike a fixed-modulus sieve, this controls every inverse exponent.
3. `critical_hub_log_depth`: every genuine `GAncestor` of the hub has an inverse exponent `t<=Nat.log2(n+2)`. This logarithmic bound is a universal numerical certificate for the entire first inverse fan-out and is independent of the large value of `2^n`.

The finite (2)-adic valuation lemma of Agent 4 (in `im-results/agent4-p1-cone2398/ValuationBound.lean`) is a generic predecessor-depth bound; our new part is the exact special-index arithmetic `v₂(7*2^n-n-2)=v₂(n+2)`, plus finite enumeration and its blank-reachability bridge. These theorems supply more precise foundations for a reflected parametric inverse-cone verifier, particularly for the many computationally closed P1 residue families.

## Open mathematical barrier

A finite first-level inverse list and its exact 2-adic depth do not exclude the positive-c feeder branches. Descendant reachability remains universally open across most critical-index residue classes. An actual P1 nonhalting decision would require an inductively closed inverse cone for **all** remaining critical indices, or a forward invariant excluding all gateways. The exact BB(6) value remains unknown.

Preserve these structural and software-enabling findings under `im-results/`, rather than promoting them to `results/` as a new solved holdout.

## Major new all-index residue exclusion: n congruent 6 modulo 16

**Source-verified in [manual Lean CI run 41431134143](https://github.com/FlareZ123/bb6/actions/runs/41431134143)**, 2026-11-02. The theorem `BB6.Agent47P1.blank_no_critical_6_mod16 (h : Nat)` establishes, against the unmodified original Agent1 and Agent50 source definitions:

```lean
∀ h : Nat, ¬ BB6.Agent1.Reach 2
  (14*2^(16*h+6)-2*(16*h+6)-10)
```

This eliminates **the complete previously unresolved critical-index class n≡6 (mod16)** for the P1 machine. Alongside Agent50's original complete n≡10(mod16) exclusion and existing n≡0,1,3,4,5,7,8,9,11,12,13,15 (mod16) exclusions, the possible P1 critical indices now lie only in **n≡2 or 14 (mod16)**, with small n=2 separately excluded by existing proofs. The original raw six-state machine to Agent1 map equivalence was established in other agents' source-checked work; our theorem is a source-level blank-reach theorem under that existing semantics, not an independent raw-machine-to-accelerator rederivation.

The proof relies on **three hubs uniformly for all h**, rather than a large index modulus or thousands of individual classes. Let X=2^(16h), u=28X-h-2 (with u≥3). The critical hub `(H(16h+6)-6,3)` is exactly `(32u+36,3)`. Exhaustive true G-ancestor inverses produce just three nonterminal hubs:

- Root `(32u+36,3)`: four predecessor branches, a continuation `(16u+12,16u+25)`, two impossible positive-mod4 leaves, and a power-of-two leaf with `x+12=30u+40`.
- Middle `(16u+12,16u+25)`: two branches, a continuation `(8u,24u+35)` and power leaf `20u+28`.
- Bottom `(8u,24u+35)`: two branches, a forbidden positive-mod4 leaf and power leaf `18u+24`.

The three power-leaf expressions are

```text
30u+40 = 840 X - 30h - 20
20u+28 = 560 X - 20h - 12
18u+24 = 504 X - 18h - 12.
```

Using X≥h+1, each is strictly between `448X=14*2^(16h+5)` and `896X=14*2^(16h+6)`, so cannot equal `14*2^j` for any j. The original-source finite predecessor algorithm and generic `Agent4Cone.Blocked` inductive soundness prove exhaustiveness and all-time unreachability. `P1SixAffine.lean` proves every inverse branch is in the stated finite list, `P1SixBlocked.lean` constructs a finite three-hub `Blocked` proof, `P1SixGap.lean` proves the power gaps and critical-root identity, and `P1SixFinal.lean` invokes original-source `positive_G_feeder` and `critical_target_implies_three` to reach the actual `Reach 2 H(n)` conclusion.

The latest CI run compiles original unmodified `GParity,GInverse,PosEvenForm,ResetGate,P1Triple,P1ResidualArithmetic,P1ResidualReach,P1Gate`, Agent4's original `ConeKernel`, and every one of our modules including the new four. `#print axioms` of `blank_no_critical_6_mod16` reports only `[propext, Classical.choice, Quot.sound]`, with **no sorryAx**. This is an all-natural rigorous mathematical result, no numerical horizon, and **still not a P1 or BB(6) nonhalting proof**.
