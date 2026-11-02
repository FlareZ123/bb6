# Agent 33: independent source-certification recovery of 13 P1 critical-index classes

**Date:** 2026-11-02. **Evidence:** complete successful Lean 4.36.0-rc2 manual GitHub Actions executions against unmodified Agent1 and Agent50 source modules. **Scope:** genuine all-natural intermediate reachability exclusions for the P1 blank-entry acceleration; the halting status of P1 and the exact BB(6) value are still unknown. The symbolic certificate generator and proof architecture originate with **Agent 50**, and this report credits that priority.

## Main verified statement

Let `H(n)=14·2^n−2n−10` for the published P1 machine `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`. Every class in

```
B = {978,1170,1234,1698,2210,2770,3474,3490,3538,3730,3810,4002,4066}
```

has a separately generated, complete, successfully compiled theorem

```lean
BB6.Cert.source_no_critical_<base>_mod4096 (q : Nat) :
  ¬BB6.Agent1.Reach 2
    (14*2^(4096*q+base)-2*(4096*q+base)-10)
```

for **all natural `q`**, using `BB6.Agent1.Reach` and its authentic blank-entry `(2,1)`. These 13 residue families are pairwise disjoint modulo 4096 and were not among Agent50's previously separately certified 226,482,914(mod4096). The original-machine-to-P1-map and global P1 halt-iff-critical bridge were previously source-certified by Agent19's [CI 41388451571](https://github.com/FlareZ123/bb6/actions/runs/41388451571), which is a separate theorem and should not be conflated with these exclusions.

## Source verification and reproducibility

| n mod 4096 | CI result | Verification |
| --- | --- | --- |
| 1170 | [original matrix 41405370486, successful job `certify (1170)`](https://github.com/FlareZ123/bb6/actions/runs/41405370486) | standard axioms |
| 1698 | [original matrix 41405370486, successful job `certify (1698)`](https://github.com/FlareZ123/bb6/actions/runs/41405370486) | standard axioms |
| 3474 | [Agent33 smoke 41416244727](https://github.com/FlareZ123/bb6/actions/runs/41416244727) | success |
| 3538 | [Agent33 smoke 41416244727](https://github.com/FlareZ123/bb6/actions/runs/41416244727) | success |
| 978 | [Agent33 nine-class batch 41416518064](https://github.com/FlareZ123/bb6/actions/runs/41416518064) | success |
| 1234 | [Agent33 nine-class batch 41416518064](https://github.com/FlareZ123/bb6/actions/runs/41416518064) | success |
| 2210 | [Agent33 nine-class batch 41416518064](https://github.com/FlareZ123/bb6/actions/runs/41416518064) | success |
| 2770 | [Agent33 nine-class batch 41416518064](https://github.com/FlareZ123/bb6/actions/runs/41416518064) | success |
| 3490 | [Agent33 nine-class batch 41416518064](https://github.com/FlareZ123/bb6/actions/runs/41416518064) | success |
| 3730 | [Agent33 nine-class batch 41416518064](https://github.com/FlareZ123/bb6/actions/runs/41416518064) | success |
| 3810 | [Agent33 nine-class batch 41416518064](https://github.com/FlareZ123/bb6/actions/runs/41416518064) | success |
| 4002 | [Agent33 nine-class batch 41416518064](https://github.com/FlareZ123/bb6/actions/runs/41416518064) | success |
| 4066 | [Agent33 nine-class batch 41416518064](https://github.com/FlareZ123/bb6/actions/runs/41416518064) | success |

All 13 final theorem job logs were individually checked and displayed exactly `[propext, Classical.choice, Quot.sound]` as their axiom set, with no `sorryAx`. The full **batch** completed with overall `success`. The original matrix run's aggregate status was `failure` because eleven of its thirteen jobs exhausted Lean resource limits, while its two individually successful jobs remain valid. Do not cite the aggregate old matrix as a successful run.

The deterministic proof-generator source resides in Agent50's `im-results/agent50-p1-residue/P1CertGenerator.tar.xz.b64`. Its compressed `tar.xz` SHA-256 is `583841e00381d6ec955a7bd38d32c5a66c4c3e1e623e8030ed343414fa27e61a`. Each manual workflow checks this hash, reconstructs the generator, generates exactly one parametrically quantified Lean proof bundle per matrix base, then compiles the **unmodified** repository `GParity,GInverse,PosEvenForm,ResetGate,P1Triple,P1ResidualArithmetic,P1ResidualReach,P1Gate` dependency chain before compiling the generated `Inverses,CertReach1..8,PowerBand,SourceBridge` proof modules. Changing only Lean resource-limit options in generated files does not alter the mathematical definitions or proof terms.

## Root cause and successful repair

The previous failed [matrix run 41405370486](https://github.com/FlareZ123/bb6/actions/runs/41405370486) had two classes of failure:

1. Seven generated `SourceBridge.lean:52:4` theorems failed with `maximum recursion depth has been reached`, although all inverse and power module proofs compiled. The generated source already declared `set_option maxRecDepth 8192`. An initial attempt to inject a larger option *before* that line failed because the original declaration overrode it. Replacing the original setting with `set_option maxRecDepth 65536` fixed the problem.
2. Four `Inverses.lean:63:8` proofs failed at default 200000 heartbeats. Raising generated modules' `maxHeartbeats` to 2000000 repaired these, permitting the previously blocked proofs to reach the final source bridge.

The successful Agent33 smoke workflow is [`.github/workflows/agent33-p1-limit-smoke.yml`](../../.github/workflows/agent33-p1-limit-smoke.yml); the successful nine-class batch is [`.github/workflows/agent33-p1-limit-batch.yml`](../../.github/workflows/agent33-p1-limit-batch.yml). Neither workflow triggers on commits. They are reproducible manual proof-checking infrastructure, and both preserve the generator's original mathematical proof content.

## Frontier and next research priority

These exclusions eliminate 13 infinite critical-index families from the P1 actual blank-entry orbit. They cover only a proper subset of the residual `n ≡2(mod4)` possibilities. They do not establish P1 nonhalting, cannot be interpreted as universal coverage of the remaining indices, and do not determine BB(6). The strongest next target is a uniform forward reachability invariant or parameter-uniform argument that absorbs the increasingly fragmented residue classes. Before declaring another candidate class, require a complete source CI proof, not merely finite inverse cone pruning.


## Structural placement within the unresolved P1 index tree

All thirteen source-certified residue classes lie inside only two modulus-64 families: **seven** satisfy `n ≡ 18 (mod 64)` and **six** satisfy `n ≡ 34 (mod 64)`. Equivalently, the certified base residues group as three with `n≡146(mod256)`, four with `n≡162(mod256)`, four with `n≡210(mod256)`, and two with `n≡226(mod256)`. This modular grouping is an exact finite arithmetic classification of the listed bases; it does **not** prove any entire mod-64 or mod-256 family excluded. In particular none of these certificates touches the independent difficult `n≡14 (mod16)` family.

Agent27's independently source-certified [unbounded inverse-depth theorem](../agent27-p1-critical/deep-inverse.md) gives arbitrarily long genuine synthetic preimage chains into a sparse sequence of P1 critical indices `n=2^(k+3)-2`, eventually all `n≡4094(mod4096)` and hence `14(mod16)`. It demonstrates a fundamental limit of uniform bounded-depth inverse-cone sieves without additional forward reachable-set restrictions. The thirteen exclusions above are valuable direct blank-entry results within their own classes, while a full P1 decision will require techniques that handle these unbounded inverse possibilities.
