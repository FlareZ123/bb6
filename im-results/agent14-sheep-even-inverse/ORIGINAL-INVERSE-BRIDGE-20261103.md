# Original-source Sheep even-return inverse gateway

Agent 14, 2026-11-03. **Intermediate formally checked proof component. Sheep and BB(6) remain open.**

## Exact all-time theorem

Lean files:
- [SheepEvenInverseAlgebra.lean](SheepEvenInverseAlgebra.lean), the generic and exceptional predecessor equations.
- [SheepEvenSourceAlgebra.lean](SheepEvenSourceAlgebra.lean), a proof from the authentic Agent16 `SheepEven.Step` and `EvenEdge` definitions.
- [SheepEvenReachInverse.lean](SheepEvenReachInverse.lean), the theorem `blank_even_inverse_cases`, preserving genuine `EvenReach 10 x` for the last predecessor of every reachable noninitial rational-power target.

For any actual `EvenReach 10 y` with `y ≠ 10`, `d*y+c=2^n`, there is an even-reachable last parent `x`. Define `D=d*3^h`. The source-complete alternatives are:

Generic: `x=2^a*v`, `a≥1`, odd `v≥5`, and

```
D*(2^(a+1)+1)*v + 2*a*D + 2^(h+1)*(d+c)
  = 2^(n+h+1)+3*D.
```

Exceptional: `x=3*2^a`, `a≥1`, and

```
D*(3*2^a+a+2) + 2^h*(d+c) = 2^(n+h).
```

Both retain an odd `u` satisfying `y=1+3^h*u`. This exact universal necessary split follows by induction on the last edge of the original `EvenReach` relation, with no finite-horizon assumption. It is available for the three existing r=138 inverse-cone targets.

Local Lean 4.36.0-rc2 compiled all three files against the **original hash-pinned Agent16 Lean archive** modules `SheepEven.lean`, `EvenEdge.lean`, `OddPrefix.lean`, `EvenReach.lean`. The final axiom audit reports `[propext, Classical.choice, Quot.sound]`, without sorry or axiomatized source signatures. Reconstruct modules using `im-results/agent16-sheep-even-return/reconstruct_all.py`. Agent16's earlier original six-state-machine semantic bridge passed source-level [CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547).

## Earlier cutoff correction

The previous `UniformH.lean` lemma `root138_node0_hstop` proved an exponent `141+4860*k` modular property; the r=138 root h≥3 inverse requires `2^(138+4860*k)%27 ≠1`. Corrected in commit `e7bd19c828d0a78f978222caad20a8a28c363684`. The old statement was true but applied to the wrong symbolic target. The corrected modular property follows from `2^18%27=1` and `4860=18*270`. No counterexample to the underlying written exclusion was found.

## Verification status and missing result

The expanded existing [manual source workflow](../../.github/workflows/agent22-sheep-source-bridge.yml) includes these modules. First dispatch [41639176407](https://github.com/FlareZ123/bb6/actions/runs/41639176407) failed in three seconds; the logs returned HTTP 404, so this was **not a new original-upstream CI verification**. No blind rerun was attempted. Local kernel verification against unmodified archived source is successful.

The full `∀k, ¬EvenReach 10 (2^(138+4860*k))` theorem still needs a Lean proof combining the present exact source gateway with low-a modular, all-large-a, high-h, exceptional, and rational-child closures. Earlier written proof and executable checker `uniform_138.py` remain the baseline. This is a genuine source-checkable integration step; external novelty has not been assessed. Keep in `im-results/`. Next work should construct the r=138 source predecessor classification using the corrected h cutoff, without new residue enumeration.

## Complete authentic r=138 root predecessor classification (later same day)

A further formalization has now closed **every** generic branch of the root except the two previously conjectured rational children. The fully Lean-kernel-checked theorem `Sheep138RootTwoChildren.root_reaches_one_child` states:

```
∀ k, SheepEven.EvenReach 10 (2^(138+4860*k)) →
  (∃ x, SheepEven.EvenReach 10 x ∧ 15*x+2=2^(141+4860*k)) ∨
  (∃ x, SheepEven.EvenReach 10 x ∧ 81*x+68=2^(143+4860*k))
```

The parent `x` in **both** alternatives is an actual earlier state reachable from authentic blank-even entry 10. The proof is all-time and uniform in `k`, and does not replace reachability with abstract synthetic solvability. The original-source exact generic/special gateway first eliminates every special branch. A new signed odd modular-gap lemma, `SheepOddGap.no_power_signed_small_odd`, together with existing `HighBound.lean`, reduces the generic last-parent alternatives to (h,a)=(0,1), (1,1..4), and (2,1..6). Nine standalone exact modular theorems then exclude all the low cases except (1,1) and (2,2). The remaining two yield the displayed rational child equations by exact algebra. All independent Lean `#print axioms` audits showed only standard axioms. In particular, the source-level final theorem has audit `[propext, Classical.choice, Quot.sound]`, with no sorryAx.

The module `Sheep138GenericHigh.lean` contains the source-level finite-a theorem and `SheepOddGap.lean` its fully proved all-exponent sign gap. The four subsequent exact modules `Sheep138LowResidues.lean`, `Sheep138RootParents.lean`, `Sheep138RootCases.lean`, and `Sheep138RootTwoChildren.lean` are losslessly archived as [root138-lean.tar.xz.b64](root138-lean.tar.xz.b64), reconstructed by [reconstruct_root138.py](reconstruct_root138.py) with SHA256 verification, atomic writes, and locks.

Archive SHA256 (compressed bytes): `7d04563403974f70067a496a51ddf2b77a23e06ba5bb8a9bda2a371ca7cfbb9a`. Individual Lean source hashes are pinned in the reconstruction script. Build in module order, after the original Sheep archive and our gateway modules. This construction stays under `im-results/` because neither child has been universally excluded in a complete source-level Lean proof. The original machine and BB(6) remain undecided. The independent original-machine pinned-version CI runner has not yet succeeded on these new modules.

The two child families have also acquired a complete source-linked **exceptional-branch exclusion** and h-bounds (first child h<4; second h<2) via `Sheep138ChildHighH.lean`, `SheepExceptionalGap.lean`, `Sheep138ChildExceptional.lean`, and `Sheep138ChildGateway.lean`. The next mathematical work is to prove the remaining generic high-a and low-a modular disqualifications for the two children, then combine them with `root_reaches_one_child` to complete the r=138 class.

## Final November 3 result: complete kernel-proved all-k r138 nonreachability

The originally open proof-integration obligation described above **has now been discharged locally**. The exact theorem, against authentic blank-section reachability, is:

```lean
theorem Sheep138FullClass.root138_unreachable (k : Nat) :
    ¬ SheepEven.EvenReach 10 (2^(138+4860*k))
```

Lean 4.36.0-rc2 compiled this theorem in [Sheep138FullClass.lean](Sheep138FullClass.lean), from the unmodified SHA-verified original Agent16 Sheep `Step`, `EvenEdge`, `EvenReach` modules and the checked mathematical chain described in this report. `#print axioms root138_unreachable` returned **`[propext, Classical.choice, Quot.sound]`**, with no `sorryAx`. Its dependent `child1_unreachable` and `child2_unreachable` have the same standard axiom audit. The proof is all-time and universal in k; no finite simulation cutoff or external untrusted oracle appears in the theorem.

A new exact source-level bridge `Sheep138ChildFinite.lean` bounds generic last parents of the first rational child to h=0/a<8, h=1/a<10, h=2/a<12, h=3/a<14; the second child to h=0/a<11 or h=1/a<13. The proof of these strict bounds is `Sheep138ChildGenericHigh.lean`, which extends the signed odd-gap inequality and the existing high-a bounds to both child targets. These two modules are losslessly archived as [child138-high.tar.xz.b64](child138-high.tar.xz.b64), restored with hash verification and locked atomic file replacement using [reconstruct_child138_high.py](reconstruct_child138_high.py); archive SHA256 `f21beab20a4265cc54e7777423d334f9428cca36f5ca1c457a7055d077defc7e`.

The 62 remaining child low-a pairs are excluded by 62 **uniform all-k parity-correct modulus-period certificates**, corresponding to 221 explicitly certified period representatives. Their `Sheep138ChildLowResidues.lean` module compiled with all 62 `#print axioms` reports `[propext, Quot.sound]`; `Sheep138ChildLowCases.lean` then establishes that each actual generic `Step` source contradicts its appropriate residue theorem, with the same audit. The final `Sheep138FullClass.lean` exhausts all these cases and combines two rational child unreachability proofs with the original-root two-child theorem. All three checked files are **deterministically regenerated and SHA256 verified** by [generate_full138.py](generate_full138.py), using the already hash-pinned upstream `Sheep138LowResidues.lean`. Expected generated SHA256 values:

- `Sheep138ChildLowResidues.lean`: `7ce461415631229b433c9b0951081f5b4d7d2e2159e5f408857628d4b51f242a`
- `Sheep138ChildLowCases.lean`: `caf6d6fd00e8ecdf8fd668800d4f9622073f5af9f9020ffd0a5ce5b34dc03339`
- `Sheep138FullClass.lean`: `6312806560d958861720f016d9fd048faec7163f9fb1dc3d078fde62e72218dd`

The existing [manual source-CI workflow](../../.github/workflows/agent22-sheep-source-bridge.yml) now restores, generates, and builds this entire chain. A **new CI success has not been obtained**, because the earlier source workflow dispatch [41639176407](https://github.com/FlareZ123/bb6/actions/runs/41639176407) failed in runner initialization with unreadable logs. Distinguish the **successful local Lean-kernel proof with original source imports** from pending pinned-version CI.

This theorem is an infinite congruence-family exclusion within one hard machine, **not a proof that Sheep does not halt**, because the other possible power exponents remain. It does not establish a universal BB(6) upper bound or exact BB(6). External novelty and independent adversarial review remain to be assessed; the proof is kept in `im-results/` accordingly.


## GitHub original-source pin verification, 2026-11-03 19:01 UTC

The earlier pending CI verification has **now succeeded for the entire Agent14 r138 proof chain**, within the manually dispatched [GitHub Actions run 41697791436](https://github.com/FlareZ123/bb6/actions/runs/41697791436), job [126132808019](https://github.com/FlareZ123/bb6/actions/runs/41697791436/job/126132808019), head SHA `1611f3f24e45ea5843f99ee0662cea05f1b6245c`. The actual hosted Ubuntu runner completed the upstream original Sheep-machine build using Cryptids revision `ced8f9f44f67a167d5ecc03e687b048c67926371` and Lean `4.35.0-rc4`, reconstructed the hash-pinned Agent16 and Agent14 Lean sources, compiled all 62 child low-a proofs, and printed the full final theorem's axiom audit:

```text
'Sheep138FullClass.root138_unreachable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Sheep138FullClass.child1_unreachable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Sheep138FullClass.child2_unreachable' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The workflow as a whole concluded **failure**, because an independent *later* Agent16 `ExceptionalEight.lean` step (lines 51 and 65) passed a natural `j` where `uniform_special_parent_absent` expected an outstanding proof term; the affected `special_5` and `special_7` emitted `sorryAx` following type errors. These later errors do not affect the already completed and axiom-audited `Sheep138FullClass` compilation. No full-workflow success is asserted.

**Consequent evidence upgrade:** the previously local Lean 4.36.0-rc2 result is now additionally verified by an actual, pinned original-source GitHub runner on Lean 4.35.0-rc4. Combined with Agent16's prior successful original-machine-to-even-return bridge [41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547), the infinite r138 power-gate exclusion is source-connected to the authentic blank Sheep machine. It remains a single infinite family and does not settle the machine or BB(6).

Other three infinite power families and the stronger complete seed-independent three-state basin characterization appear in [ROOT-FREE-CONES.md](ROOT-FREE-CONES.md) and [exact_cones.py](exact_cones.py); these remain paper-plus-exhaustive-modular certificates, with no all-family Lean theorem claimed.
