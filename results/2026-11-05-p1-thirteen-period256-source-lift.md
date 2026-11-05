# Thirteen source-certified period-256 P1 critical exclusions

**Agent 8, incorporating Agent 45's original parametric arithmetic discovery. 2026-11-05.** Actual blank-reachability necessary-gateway theorem; P1 and BB(6) remain undecided.

## Mathematical result

Define `H(n)=14*2^n-2*n-10`. For each `q0` in the following set and for **every** natural `r`, the unchanged original P1 accelerated blank-entry reachability predicate satisfies:

`¬ BB6.Agent1.Reach 2 (H(16*q0+2+4096*r))`.

The 13 pairwise disjoint residue classes (modulo 4096) are:

| q0 (mod 256) | excluded n (mod 4096) | finite arithmetic certificate | original-source final theorem |
|---:|---:|---|---|
| 61 | 978 | [BatchQ61.lean](../im-results/agent8-p1-q256-batch/BatchQ61.lean) | [BatchQ61Final.lean](../im-results/agent8-p1-q256-batch/BatchQ61Final.lean) |
| 73 | 1170 | [BatchQ73.lean](../im-results/agent8-p1-q256-batch/BatchQ73.lean) | [BatchQ73Final.lean](../im-results/agent8-p1-q256-batch/BatchQ73Final.lean) |
| 77 | 1234 | [BatchQ77.lean](../im-results/agent8-p1-q256-batch/BatchQ77.lean) | [BatchQ77Final.lean](../im-results/agent8-p1-q256-batch/BatchQ77Final.lean) |
| 106 | 1698 | [BatchQ106.lean](../im-results/agent8-p1-q256-batch/BatchQ106.lean) | [BatchQ106Final.lean](../im-results/agent8-p1-q256-batch/BatchQ106Final.lean) |
| 138 | 2210 | [BatchQ138.lean](../im-results/agent8-p1-q256-batch/BatchQ138.lean) | [BatchQ138Final.lean](../im-results/agent8-p1-q256-batch/BatchQ138Final.lean) |
| 173 | 2770 | [BatchQ173.lean](../im-results/agent8-p1-q256-batch/BatchQ173.lean) | [BatchQ173Final.lean](../im-results/agent8-p1-q256-batch/BatchQ173Final.lean) |
| 217 | 3474 | [BatchQ217.lean](../im-results/agent8-p1-q256-batch/BatchQ217.lean) | [BatchQ217Final.lean](../im-results/agent8-p1-q256-batch/BatchQ217Final.lean) |
| 218 | 3490 | [BatchQ218.lean](../im-results/agent8-p1-q256-batch/BatchQ218.lean) | [BatchQ218Final.lean](../im-results/agent8-p1-q256-batch/BatchQ218Final.lean) |
| 221 | 3538 | [BatchQ221.lean](../im-results/agent8-p1-q256-batch/BatchQ221.lean) | [BatchQ221Final.lean](../im-results/agent8-p1-q256-batch/BatchQ221Final.lean) |
| 233 | 3730 | [BatchQ233.lean](../im-results/agent8-p1-q256-batch/BatchQ233.lean) | [BatchQ233Final.lean](../im-results/agent8-p1-q256-batch/BatchQ233Final.lean) |
| 238 | 3810 | [BatchQ238.lean](../im-results/agent8-p1-q256-batch/BatchQ238.lean) | [BatchQ238Final.lean](../im-results/agent8-p1-q256-batch/BatchQ238Final.lean) |
| 250 | 4002 | [BatchQ250.lean](../im-results/agent8-p1-q256-batch/BatchQ250.lean) | [BatchQ250Final.lean](../im-results/agent8-p1-q256-batch/BatchQ250Final.lean) |
| 254 | 4066 | [BatchQ254.lean](../im-results/agent8-p1-q256-batch/BatchQ254.lean) | [BatchQ254Final.lean](../im-results/agent8-p1-q256-batch/BatchQ254Final.lean) |

The final Lean declaration is `BB6.Agent8BatchQ<q0>.critical_<16*q0+2>_mod4096_unreachable`, in the listed source. Every one of the 13 files is checked by [manual original-source Lean CI 42110442046](https://github.com/FlareZ123/bb6/actions/runs/42110442046), including unmodified Agent1/4/9/45/47/50 definitions, `GenericBlocked`, `GenericShadow` and `GenericCritical`. **All 13 final theorems** print exactly `[propext, Classical.choice, Quot.sound]`; there are no admitted axioms or `sorryAx`.

## Mathematics and source boundary

Agent45's earlier [q61 affine cylinder research](../im-results/agent45-p1-q61-cylinder/README.md) identified the thirteen period-256 graph families and locally verified arithmetic closure for their respective two inverse roots. This work independently regenerated their small explicit lists and, crucially, **connected every one to true original-source P1 blank-root unreachability**. The external-original-source bridge is the general theorem `BB6.Agent8Generic.critical_unreachable_of_shadow`, independently verified in [manual CI 42109123502](https://github.com/FlareZ123/bb6/actions/runs/42109123502).

For `q=q0+256r`, the two feeders are `(4u-4,4u+9)` and `(6u-2,2u+5)` with `u+4q+3=7*2^(16q)`. Every authentic odd backward path is projected into a **finite affine graph** in coordinates `(m,z)`. The transition has `z=2^t*v`, `2*z'+1=16q+h+m+t+v`, `(m,z)→(m+t+1,z')`, with `h=8,9` respectively. Each family has exactly 22 total affine states over both feeders (9+13, 11+11, or 13+9), maximal cost `m≤9`, hence satisfies the generic theorem's `m≤10` condition. The lists contain no state with `256∣z`. They are closed under all parametrically possible successors for **all** natural r and inverse depths. Generic source lemmas use that closure plus the original `GAncestor` inverse completeness, power gate barrier and exact two-feeder iff to exclude the real blank-orbit critical target.

The 13 arithmetic families were **prior observations by Agent45**. Authenticated blank-source terminal closure and the batch of 13 final original-source proofs are this integration's value. Since external literature and other newly evolving repository results have not been exhaustively checked, novelty beyond the repository is not guaranteed.

## Limitations

Each proved class comprises only the *necessary* critical target family for one still-undecided P1 machine; the full sector of remaining critical exponents is infinite, and other six-state holdouts remain. There is no universal BB(6) upper bound, no full machine classification, and no exact BB(6) value. Also do not count q residues beyond the 13 actually kernel-verified classes. The exploratory prior Agent12 787-candidate aggregate is not a theorem.

Reproduction: [source directory](../im-results/agent8-p1-q256-batch/README.md), [manual workflow](../.github/workflows/agent8-p1-q256-batch-source.yml), [CI 42110442046](https://github.com/FlareZ123/bb6/actions/runs/42110442046).
