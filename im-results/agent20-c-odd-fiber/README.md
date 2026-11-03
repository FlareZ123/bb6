# Exact predecessor fibers of Machine C's low halting gateway (Agent 20)

**Source-certified intermediate mathematical result; BB(6) is unresolved.** This theorem refines the exact one-step inverse structure of the real accelerated Machine C zero-high section and applies it to actual section-halting inputs. An incoming section edge does not imply any genuine blank-origin orbit reaches the target.

## Original source and quantified theorems

Machine C RLE: `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`. The original accelerated section map is `BB6.Agent46.secNext` from `im-results/agent46-c-jump/FastSectionDef.lean`, with `bounce` in `BounceCalc.lean`. Its genuine blank section starts at `(5,1)`. Agent3's original-source `section_preimage_all_iff` and `PowerDegreeExact.lean` give a complete inverse grammar, including arbitrarily deep bounce branches.

**Generic odd target:** For every natural `t>=1`, and odd integer `C>=5`, put `Y=4^t*C-1`. For each `r=0,...,t-1`, define

```text
a_r = 2*4^r*C - 2
k_r = Y - 4^r*C - 3*(t-r-1) - 2
```

Then `secNext(a_r,k_r)=some(1,Y)`; these `t` source pairs are distinct, and **every** source `(a,k)` with `secNext(a,k)=some(1,Y)` is exactly one of them. The theorem `BB6.Agent20OddFan.odd_target_fiber_exact` supplies the complete injective `Fin t` parametrization, and `odd_target_preimages_iff` gives the explicit all-input iff. The proof exhausts exceptional, direct, odd-bounce, and even-bounce cases, with no recurrence-depth cutoff.

**Low halting family specialization:** For all `t>=1` and `m+1=4^t`, put `K_m=2^(2*m+3)-3*m-4` and `C=2*4^(m-t+1)-3`. The theorem `low_gate_four_factor` shows `K_m+1=4^t*C`, with `C>=5` odd. Hence `low_gate_exact_fiber` proves the corresponding low halting input `(1,K_m)` has *exactly t* incoming accelerated section edges. The separate `LowHaltWitness.lean` theorem `low_gate_halts` invokes Agent15's original-source `section_halts_iff_parametric` to prove `secNext(1,K_m)=none`. Their conjunction `low_four_power_halt_fiber` proves all these properties simultaneously.

This yields halting-section inputs with **unbounded exact in-degree**, a stronger targeted result than the prior balanced synthetic-target fan. It proves neither blank reachability nor nonreachability and therefore leaves Machine C and BB(6) open. In particular the existence of many synthetic predecessors is not evidence that the target is on the actual blank orbit.

## Formal verification and reproducibility

- Full Lean 4.36.0-rc2 **[successful manual original-source CI 41565353035](https://github.com/FlareZ123/bb6/actions/runs/41565353035)**, head `2502d34d63fdbf002d012f82be5e5ee2726a4adf`, job `125685443342`. The workflow `.github/workflows/agent3-c-bounce-inverse.yml`, `workflow_dispatch(balanced_only=true)`, compiles the **unmodified original** Agent46 and Agent3 proof imports, the SHA-checked new sources, then the **unmodified original** Agent15 stopping criterion source chain. All new theorems compile. The final `#print axioms` on `odd_target_fiber_exact`, `low_gate_exact_fiber`, and `low_four_power_halt_fiber` reports precisely `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.
- `OddFan.lean.xz.b64` is a compressed, base64-encoded *lossless* archive of the formal Lean source. Decode base64 and XZ; original source SHA256 `bf7f1c6366cc424aede82c4a4c38b77e3002f2b6c6c2dbcb62b8df798772ee8f`. It imports the original `PowerDegreeExact.lean`. `LowHaltWitness.lean` is plain source; SHA256 `d7cc7f78d72324d7253f6e2dd486f5299c3386bf407f89d14944975cc21c5ad2`.
- Supporting manual finite test: source-independent exact arithmetic inverse enumerator matched every expected `(1,4^t*C-1)` source for small `t`, odd `C`; the formal proof is universal and does not depend on the enumerator.
- This extends Agent11's `Fan` exploration and Agent3's known complete inverse grammar `SectionAllInverse.lean`. The balanced synthetic-target exact count `t+3` was source-certified separately in the same run and [41563298317](https://github.com/FlareZ123/bb6/actions/runs/41563298317).

## Follow-up global mathematical question

The complete low halting equation is `K_m+3*m+4=2^(2*m+3)` for every `m`. Its full source-predecessor count appears to admit a simple 2-adic characterization. An independent Python inverse enumerator tested all `0<=m<=400` without discrepancy:

```text
m odd:  floor(v2(m+1)/2)
m even: 1 + max(0, floor((v2(3m+2)-1)/2))
```

Here `v2` is the 2-adic valuation of a positive integer. **This last all-m formula is experimental and not Lean-proved.** Derive it with exact exceptional branch and small-m handling before any claim; even a proven count will not by itself exclude genuine blank reachability. A promising successor aim is a global forward invariant or a uniform origin-infeasibility argument for the remaining halting target families.

Do not promote this module to `results/` without independent relevance and external novelty review under the research protocol.


## New source-certified all-time blank-orbit exclusion: low halting parameter m=3

The low-family input `(1,K_3)=(1,499)` is proved **unreachable at every accelerated Machine C section time starting from the genuine blank section (5,1)**. This is stronger than a finite-depth absence observation and removes one nontrivial remaining low-family halting gateway. It does **not** settle any other parameter.

The complete, exact reverse graph is:

```text
(1,499) <- (248,372) <- (618,185) <- (399,291) <- []
```

The first predecessor uniqueness follows from our earlier full `odd_target_preimages_iff` at `t=1,C=125`. The two following uniqueness theorems `m3_parent_248_372` and `m3_parent_618_185` are **original-source all-input theorems** proved directly from Agent3's exhaustive `section_preimage_all_iff`; they rule out arbitrarily deep bounce behavior using a rigorous finite exponent bound `n<=6` and case analysis. The final `(399,291)=(4*99+3,4*72+3)` is excluded from the blank orbit for all times by the previously source-certified Agent38 `blank_section_no_33` theorem. Exact deterministic section-run induction then yields `BB6.Agent20OddFan.m3_unreachable`.

**[Original-source CI run 41567591797](https://github.com/FlareZ123/bb6/actions/runs/41567591797) passed** at commit `79d154e3645ae5d4235f10d8975f822997493081`, Lean 4.36.0-rc2. All three theorem axiom audits `m3_parent_248_372`, `m3_parent_618_185`, and `m3_unreachable` report exactly `[propext, Classical.choice, Quot.sound]`: no `sorryAx`, no source signature mocks. Certified complete proof is `LowM3.lean.xz.b64` (base64+XZ-encoded original Lean source), uncompressed SHA256 `554c93a6d05d776a628a8083ac1235ab0b54b6d4f919d6d66c3f2d7b0866ed5d`. The same CI also certified the **uniform all-m predecessor parity theorem** `low_gate_parent_parity`, where every source `(a,k)` with `secNext(a,k)=some(1,K_m)` satisfies `(a+m)%2=1`. Its original-source Lean certificate is `LowParity.lean.xz.b64`, source SHA256 `724a3d620e46cc42f83af58c4b372dcc60f76ad276e9d5b5c0efc31001497ed0` and CI [41566674344](https://github.com/FlareZ123/bb6/actions/runs/41566674344) plus [41567591797](https://github.com/FlareZ123/bb6/actions/runs/41567591797).

The exact reverse graph was first observed with an independent small-integer Python enumerator; the quoted all-time exclusions are now kernel-checked source-based proofs. The global question remains open because `m=3` is one point in an **infinite** two-family halting locus.
