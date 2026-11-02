# Machine C: candidate new M16 forbidden section cylinders and stopping parameters

**Agent41, 2026-11-02.** Verification status at initial writing: full original-source compiled Lean **pending** in manual CI [41478417628](https://github.com/FlareZ123/bb6/actions/runs/41478417628). The unchanged Agent43 M16 certificate **also rebuilt successfully in Agent41's manual full-original-source run [41474400130](https://github.com/FlareZ123/bb6/actions/runs/41474400130)**; its prior independent original-source CI was [41412951906](https://github.com/FlareZ123/bb6/actions/runs/41412951906). Until the new CI succeeds, **treat these new target exclusions as computational candidates**, not established new all-time theorems.

Machine C remains unclassified; BB(6) remains open. Source machine: Agent11's unmodified `BB6CLine.nextC`, blank-origin entry `(5,0,1)`. Exact stopping-parameter equations: Agent15's two-parameter source analysis, [Agent15 report](../agent15-c-halting/README.md).

## Finite certificate and independent computation

Agent43's modulus-16 quotient has base 8, q(x)=x below 8, otherwise q(x)=8+((x-8)%16). The source-checkable proof exhaustively checks **13,824** abstract vertices, with **7,115** reached and **34,992** representative transitions. All finite edges and the correspondence to every original real counter step are checked by Lean's kernel and soundness lemmas. A blank-origin true reachable triple must project to a reached abstract triple. Original [Agent43 M16 documentation](../agent43-c-quotient-kernel/M16.md).

Independent C++ and JavaScript finite-quotient engines, plus a third Python experiment, reproduce the same 7,115 abstract vertices. The following source-level candidate absences are found in the computed finite closure:

1. All **six** q16 states (a in {1,9,17}, k in {2,18}, c=0) absent. Therefore the entire infinite cylinder `(a,k,c)=(8u+1,16v+2,0)` would be forbidden for all `u,v>=0`.
2. The state (9,15,0) absent. Therefore `(16u+9,16v+15,0)` would be forbidden for all `u,v>=0`.
3. The states (1,23,0), (17,7,0), and (17,23,0) absent, whereas (1,7,0) is **present**. Thus the precise candidate exclusion is `(16u+1,16v+7,0)` whenever `u>0 or v>0`; the exceptional pair u=v=0 must **not** be excluded by this certificate.

These three statements are encoded, without `sorry`, in [Mod16OneTwo.lean](./Mod16OneTwo.lean) using Agent43's exact original CLine source bridge and finite closure.

## New candidate residue restrictions on Agent15's exact immediate-stopping equation

For the odd-first-counter family `a=2j+3`, with `k+j+3m+5=2^(2m+2)*(j+3)`, the candidate source theorems in `Mod16OneTwo.lean` exclude:

| Parameter restriction | Corresponding target congruence | Number of j,m classes modulo 16 |
|---|---|---:|
| `j%4=3`, `(m+1)%16=j%16` | a%8=1, k%16=2 | 4 |
| `j%8=3`, `m%16=j%16` | a%16=9, k%16=15 | 2 |
| `j%8=7`, `(m+8)%16=j%16` | a%16=1, k%16=7; a>=17 | 2 |

All **eight** parameter classes are disjoint from the two M8 excluded classes `(j%8,m%8)=(2,7),(6,3)`. Their k values have even k and a+k≡3(mod4), or odd k and a+k≡0(mod8), avoiding Agent38's simplest prior odd-counter exclusion. Independently compiled local Lean arithmetic checks the divisibility and modulo equations.

For the first-family stopping equation `a=1, k+3m+4=2^(2m+3)`, additional **candidate depth families** are `m%16=14` (then k%16=2) and `m%16=7` (then k%16=7 with k>=23). A complete candidate `published_no_first_halt_m7_or_14` proof source is [Mod16First.lean](./Mod16First.lean). Its arithmetic proof compiled locally using a development-only stub for the M16 reachability theorems. **This is not a trusted original-source certificate until the full CI compiles both files.** The [manual CI workflow](../../.github/workflows/agent41-c-mod16-odd-two.yml) is now configured to compile both.

## Trust boundary, reproduction and next actions

The exact actual-source verification run for the first 3 cylinders and 3 odd halting parameter theorems is [41478417628](https://github.com/FlareZ123/bb6/actions/runs/41478417628). It SHA256-verifies Agent43's original M16 archive, compiles all 24 `P16Block` kernel certificates, the full quotient soundness and reachability proofs, original `CLine.lean`, and `Mod16OneTwo.lean`, then prints theorems' axiom dependencies. Its completion must be checked before changing this report's status. The current run **41478417628** uses the updated workflow to compile both `Mod16OneTwo.lean` and `Mod16First.lean` from unmodified original sources. The earlier candidate run 41476553529 was intentionally cancelled after detecting and correcting its outdated `source_reachable_embeds` theorem reference to Agent43's actual M16 `source_reachable_embeds16`.

These are conditional partial restrictions on one BB(6) holdout. They do **not** prove a universal upper bound on halting times, complete Machine C's nonhalting proof, or determine the exact value of BB(6).

## De-duplication audit: which M16 gains are genuine?

An independent complete B8/M8 vs B8/M16 finite quotient comparison across the Agent15 odd-first-counter equation's 16-by-16 large-exponent residue torus finds **20** M16-absent parameter pairs that were still admitted by M8. They partition exactly into:

- **Four even-k, sum-3 pairs:** (j,m) mod16 = {(3,2),(7,6),(11,10),(15,14)}. These are the first new cylinder proved by `published_no_even_odd_halt_params` if the original-source CI succeeds.
- **Four odd-k, sum-0 pairs for j≡3 or7 mod8:** {(3,3),(11,11),(7,15),(15,7)}. These are covered by the other two new conditional source theorems.
- **Eight odd-k, sum-0 pairs with j even:** {(0,6),(2,4),(4,2),(6,0),(8,14),(10,12),(12,10),(14,8)}. These already satisfy Agent38's source-certified `blank_section_no_odd_special`: both odd, `(a+k)%8=4` and `(a+3k)%16=14`, so we do **not** count them as new proof targets.
- **Four even-k, sum-1 pairs:** {(2,5),(6,9),(10,13),(14,1)}. All have `a%8=7` and `k%16=10`. Under Agent15's **already source-certified** all-input affine predecessor map for `k≥4`, even k, `(a+k)%4=1`, any blank-reachable target (a,k) has its unique blank-reachable precursor `(a+k-2,(k-2)/2)`, which lies in Agent41's **already fully Lean-certified M8 forbidden cylinder** `(8u+7,8v+4)`. This is a rigorous mathematical *paper composition* of existing source theorems; the combined original `CReach` bridge has **not** yet been kernel checked as one new Lean theorem and should be formalized by Agent15.

Thus the most promising genuinely additional M16 *mathematical* restrictions are exactly **eight** residue pairs, represented in the candidate M16 Lean file. This audit prevents incorrectly claiming all 20 finite quotient gains to be novel and exposes a useful all-depth inverse closure extension of the independently kernel-checked M8 result. Their novelty relative to the whole corpus still needs collaborator review.

The 8 odd-k cases under the existing Agent38 invariant and the 4 even-k cases under Agent15 affine inverse are excluded for *all section times*, independent of the unverified M16 new-target proof. The exact original-machine composition of Agent15's return-section `CReach` and the original `BB6CLine.Reach` is documented by Agents15/46/21; recheck its hypotheses when encoding the combined theorem.
