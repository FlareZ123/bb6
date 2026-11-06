# BB429: a nonmodular blank-root obstruction, an even-16 invariant, and a 16,384-cylinder exclusion

**Status (6 November 2026): Lean-kernel certified intermediate mathematics.** The original-source audit [CI 42226859021](https://github.com/FlareZ123/bb6/actions/runs/42226859021) compiled the unchanged accelerator and preceding proof chain with Lean **4.36.0-rc2**. The pinned original Cryptids raw-TM bridge for the 11,473 modulo 16,384 exclusion [passed CI 42227361882](https://github.com/FlareZ123/bb6/actions/runs/42227361882) against upstream commit `c86f15861709b76042998c5211c7b2f83991621b` using Lean **4.35.0-rc4**. The 40-cylinder extension below passed [in-repository Lean 4.36.0-rc2 CI 42255295632](https://github.com/FlareZ123/bb6/actions/runs/42255295632); the pinned raw-source audit is queued. This work neither decides the authentic six-state machine nor determines BB(6).

## Strongest mathematical statements

Let `BB429.run n (0,0)=some(a,b)` denote the **genuine blank-root** accelerated section of six-state Cryptids machine `1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA`. All parameters below are arbitrary natural numbers and all times are unbounded.

1. [`BB429Even16.rooted_odd_three_one`](BB429Even16.lean):
   `a%4=3 ∧ b%4=1 ⟹ a=3 ∧ b≥9`. Consequently every true-root state with `a≥7, a%4=3, b%4=1` is forbidden. This is a **nonmodular boundary exception**, stronger than merely excluding terminal states with `a%4=3`.
2. [`BB429Even16.rooted_even_sixteen`](BB429Even16.lean): for `a>0` even, `a%4=0 ⟹ b%16=2`, and `a%4=2 ⟹ b%16=10`. This strengthens the preexisting true-root result `b%8=2`; it is an authentic-orbit theorem rather than a free-start congruence restriction.
3. [`BB429No11473.blank_halt_not_11473_mod16384`](BB429No11473mod16384.lean): if the genuine section `(a,b)` lies on the original exact terminal line `b+1=2*a`, then `a%16384≠11473`. Equivalently, no member of the complete infinite family `(16384q+11473,32768q+22945)`, `q:Nat`, is ever blank-reachable.
4. [`BB429ManyLifts.blank_halt_not_new_lifts`](BB429ManyLifts.lean): for the explicit 40-element set `newLifts`, every genuine blank-root terminal state satisfies `a%16384 ∉ newLifts`. Each entry has a kernel-evaluated depth-12 symbolic certificate, and `cert_sound` lifts it to all `q:Nat`. The 40 residues lie in the current 52/8192 surviving gate and are disjoint from 11,473. Relative to that 52-gate baseline, 104 lifts modulo 16,384 remain; after the 11,473 cylinder and these 40 exclusions, 63 remain. This is a refined necessary filter, not a nonhalting proof.

The third theorem **strictly extends** the previously established [Agent 1 exclusion `a%65536≠11473`](../agent1-429-root-rows/README.md): its four mod-65536 lifts are **11,473, 27,857, 44,241, and 60,625**. Prior related source proofs are Agent6 [`BB429NoThree.reachable_even_positive`](../agent6-harmonic429/BB429NoThree.lean), Agent39 [`BB429RootEven8.rooted_positive_even_eight`](../agent39-429-1021/BB429RootEven8.lean), and Agent33's [sound parametric inverse kernel](../agent33-429-24/BB429InverseKernel.lean). Attribution of any external academic novelty remains open. An inverse restriction can be mathematically stronger while still overlapping later independent terminal exclusions at finer moduli.

## Proof architecture

The exact twelve-branch source `BB429.next` admits a simple complete one-step argument: if an output has `a%4=3,b%4=1`, its predecessor must lie in the first branch, have even first coordinate `u`, and `w%4=0`. A positive even blank-reachable predecessor has `w%4=2` by Agent6, so necessarily `u=0`, forcing `a=3`. For any reached zero-first state, `w=0` at the blank origin or `w≥10` after an incoming reset. Thus the successor must have `b≥9`.

For positive even output `a`, exact branch inversion plus the prior root `w%8=2` for even parents and the new odd-three-one restriction on odd parents forces the stated unique `b%16` residue. These are exhaustive `next` branch splits handled by Lean's `omega`; there is no sampled-step assumption.

[`BB429InverseKernel16.lean`](BB429InverseKernel16.lean) extends Agent33's exact, formally sound affine all-parameter backward certificate with one extra leaf test:
```
A%4=0, B%4=0, a≥7, a%4=3, b%4=1
```
for affine ancestor `(Aq+a,Bq+b)`. The new `bad_sound` branch imports `rooted_odd_three_one`; all existing six leaf tests and their `F/S/E` inverse transition guards are unchanged. The entire `cert_sound d s q` proof is Lean-checked for every `d,s,q`, without an inverse-depth assumption.

For the terminal affine family `(16384q+11473,32768q+22945)`, a finite computation of the **symbolic tree** establishes
```lean
BB429Kernel16.cert 12 ⟨16384,11473,32768,22945⟩ = true
```
by `decide` in the kernel, then `cert_sound` universally excludes all `q`. This is different from checking twelve forward steps or a finite set of numeric input values. The extra new leaf closes a formerly surviving twelve-step inverse path; all alternative exact predecessor branches close using previously certified root predicates.

## Verification and remaining mathematical gap

- **In-repository source certification:** [successful manual GitHub Actions 42226859021](https://github.com/FlareZ123/bb6/actions/runs/42226859021), Lean 4.36.0-rc2, with all printed axiom audits clean.
- **Original Google DeepMind Cryptids raw source:** [`SourceRawHalt11473.lean`](SourceRawHalt11473.lean) passed [pinned raw-source CI 42227361882](https://github.com/FlareZ123/bb6/actions/runs/42227361882). The 40-cylinder source bridge is [`SourceRawHaltManyLifts.lean`](SourceRawHaltManyLifts.lean); its pinned workflow audit is being rerun against the corrected proof after earlier canceled attempts.
- **Reproduction:** `.github/workflows/agent30-429-many-lifts.yml` compiles the local source chain and `.github/workflows/agent30-429-many-lifts-native.yml` compiles the same theorem against unchanged pinned Cryptids. No proof uses `sorry`, `native_decide`, assumed machine steps, or a copied alternate transition function.

The certificate eliminates one **infinite necessary halting family for one outstanding machine**. Other necessary terminal cylinders remain infinite; no true-blank halting witness, machine nonhalting decision, six-state coverage certificate, or global upper bound follows. A strong next direction is adapting the new history-sensitive exception to parameter-uniform inverse cores in still-surviving regions, rather than counting redundant congruence gates.
