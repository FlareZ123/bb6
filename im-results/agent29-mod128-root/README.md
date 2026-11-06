# Exact inverse reduction for an additional Machine C dyadic sector

**Research status (6 November 2026): all individual results below are kernel-checked against the authentic, unchanged Machine C source. The global Machine C halting question and BB(6) are unresolved.** These results are stored in `im-results/` because external novelty, comprehensive overlap with the prior source filters, and a publication-ready account still require review.

## Model and trust boundary

The formalized machine is the six-state, two-symbol machine `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`. Its exact section map is `BB6.Agent46.secNext`, with actual blank-tape entry `(5,1)`. A section pair `(x,y)` satisfies `BB6.Agent3.CReach x y` precisely when some genuine blank-rooted iterate of the original section reaches that pair. We import unchanged source equations, actual-section correspondence, exact predecessor lemmas, and the established blank-odd-image obstruction. No synthetic starting orbit is assumed.

## The new exact root-relative inverse

For all naturals with `x%8=5`, `y%2=0`, `6≤y`, `(x+y+1)%128=96`, and `48≤x+y+1`:

```
CReach x y ↔ CReach (x+y-2) ((y-2)/2).
```

The original immediate-source predecessor grammar has exactly the **following necessary possibilities** in this target sector (depths one and three are the only bounce possibilities):

```
(a=x+y-2 ∧ y=2*k+2) ∨
(4*a+12=x+y+1 ∧ 2*k+a+10=x+2*y) ∨
(16*a+48=x+y+1 ∧ 2*k+a+16=x+2*y).
```

Both bounce possibilities force an alleged actual blank-root predecessor to have odd right counter at least five and coordinate sum 2 modulo 4. The already source-certified blank-odd-image theorem excludes both possibilities, while the direct parent is certified by the exact source `direct_even_section`. The `iff` therefore holds **on the actual blank orbit** even though immediate abstract source inversion branches. The proof handles all magnitudes without enumerating a time bound.

Sources: [RootMod128Arithmetic.lean](RootMod128Arithmetic.lean), [RootMod128Inverse.lean](RootMod128Inverse.lean), [RootMod128Source.lean](RootMod128Source.lean). The key statements are `section_sum96_mod128_inverse` and `sum96_forced_root_iff`.

## Three all-time forbidden infinite blank-origin cylinders

The following universal theorems exclude genuinely reachable Machine C section pairs. For all `x,y : Nat`:

| Theorem | Forbidden target restrictions | Exact ancestor chain |
| --- | --- | --- |
| `blank_no_two_link` | `x%16=13`, `(x+y+1)%128=96`, `34≤y` | New dyadic root rule, then Agent15 affine |
| `blank_no_three_link` | `x%64=37`, `(x+y+1)%128=96`, `58≤y` | New dyadic root, affine, Agent3 low-valuation odd/odd |
| `blank_no_four_link` | `x%128=117`, `(x+y+1)%128=96`, `106≤y` | New dyadic root, affine, odd/odd, Agent24 even-right |

Each chain ends at a section pair with an odd right counter at least five and forbidden coordinate sum 1 or 2 modulo 4, contradicting the authentic blank image invariant. Every source transformation is a prior, independently certified true-blank reachability **equivalence**, rather than a heuristic simulation or an affine analogy.

Arithmetic and source proofs: [RootMod128ThreeArithmetic.lean](RootMod128ThreeArithmetic.lean), [RootMod128ThreeSource.lean](RootMod128ThreeSource.lean), [RootMod128FourArithmetic.lean](RootMod128FourArithmetic.lean), [RootMod128FourSource.lean](RootMod128FourSource.lean). The congruences in the three- and four-link rows already force `y≥58` and `y≥106` respectively. [RootMod128Sharp.lean](RootMod128Sharp.lean) proves the size-guard-free congruence-only corollaries `blank_no_three_mod_only` and `blank_no_four_mod_only`, certified against the unchanged original section in [CI 42154109552](https://github.com/FlareZ123/bb6/actions/runs/42154109552), ordinary Lean axioms only.

## Consequences for the exact high halting locus

Agent15's original-source halting criterion has the high stopping equation

```
k+j+3*m+5 = 2^(2*m+2)*(j+3).
```

Under that equation, each row below implies `¬ CReach (2*j+3) k` for every natural parameter triple:

| Theorem | Additional forbidden parameter conditions | Origin |
| --- | --- | --- |
| `blank_no_high_stop_mod128` | `m≥4`, `j%8=5`, `(j+31)%128=(3*m)%128` | Two-link cylinder |
| `blank_no_high_stop_three` | `m≥4`, `j%32=17`, `(j+31)%128=(3*m)%128` | Three-link cylinder |
| `blank_no_high_stop_four` | `m≥4`, `j%64=57`, `(j+31)%128=(3*m)%128` | Four-link cylinder |
| `blank_no_high_after_seven` | `m%32=6`, `(j+51)%256=(9*m)%256` | Agent19 sum-seven inverse to two-link cylinder |

Files: [RootMod128High.lean](RootMod128High.lean), [RootMod128HighSource.lean](RootMod128HighSource.lean), [RootMod128ThreeHigh.lean](RootMod128ThreeHigh.lean), [RootMod128FourHigh.lean](RootMod128FourHigh.lean), [RootMod128AfterSevenHigh.lean](RootMod128AfterSevenHigh.lean). In the fourth case the stopping target is first backward-normalized by Agent19's distinct sum-seven rule, then its parent enters the new dyadic sector. These are **necessary stopping-input exclusions**, with no claim that any remaining parameter triple is actually attained by the blank orbit. The infinite low and remaining high stopping loci are unsolved.

## Executable source-exact normalization

[MixedSixRightNormalize.lean](MixedSixRightNormalize.lean) composes Agent24's six-even-right gate, Agent19's sum-seven gate, and the present dyadic inverse gate into one terminating `mixedSixRightNormalize` for all natural target pairs. The theorem `mixedSix_reach_iff_normalize` proves true-blank reachability is invariant. The theorem `mixedSixRightExcluded_sound` proves the resulting executable parity exclusion is sound for every genuine blank time. The weighted mass `x+2*y` decreases at each gate, and all associated source lemmas are unchanged.

## Verification

The [manual-only source-audit workflow](../../.github/workflows/agent29-mod128-root.yml) builds unchanged source CLine, `secNext`, bounce, original correspondence, odd-image and exact inverse modules with Lean **4.36.0-rc2**, then checks the files in this directory.

- [CI 42149535742](https://github.com/FlareZ123/bb6/actions/runs/42149535742): first dyadic root rule and two-link exclusion, success.
- [CI 42151463226](https://github.com/FlareZ123/bb6/actions/runs/42151463226): third link, its high family, mixed inverse normalization and sound test, success.
- [CI 42151816401](https://github.com/FlareZ123/bb6/actions/runs/42151816401): fourth link and third independent high family, success.
- [CI 42152271488](https://github.com/FlareZ123/bb6/actions/runs/42152271488): composed old sum-seven plus new dyadic high family, success.

The final original-source reachability theorems each print **only** `[propext, Classical.choice, Quot.sound]` under `#print axioms`, with no `sorryAx`, extra hypotheses on unreachable synthetic starts, or finite-time extrapolation.

The combined [JointMod128Root.lean](JointMod128Root.lean) **has also been original-source certified** as theorem `BB6.Agent29Joint.blank_halts_iff_joint_mod128`, merging all four new high families with Agent19's previously source-certified time-free halting iff. The complete separate source-audit [CI 42152686980](https://github.com/FlareZ123/bb6/actions/runs/42152686980) succeeded with final axiom list `[propext, Classical.choice, Quot.sound]`. Its infinite parameter existentials remain open. [JointNonredundant.lean](JointNonredundant.lean) **proves universally** that every pair of high stopping indices in the union of the four new families satisfies **all** of Agent19's previously combined high filters (including the unbounded dyadic restriction). Thus none of the four exclusions was already contained in that prior high sieve. [JointExplicitFamilies.lean](JointExplicitFamilies.lean) proves four separate, explicit unbounded families of such previously allowed indices:

```
(j,m) = (109+24*n, 4+8*n)
(j,m) = (17+96*n, 16+32*n)
(j,m) = (121+192*n, 8+64*n)
(j,m) = (3+288*n, 6+32*n), for every n : Nat.
```

[CI 42153832992](https://github.com/FlareZ123/bb6/actions/runs/42153832992) source-certified both `new_high_class_previously_allowed` and `four_progressions_prior_allowed` with exactly `[propext, Classical.choice, Quot.sound]` axioms. These progressions are **arithmetic stopping-input indices**, not proof of any actual blank-orbit visit or halt.

## Scientific scope and next directions

This is a new 2-adic valuation-five *root-relative* source-inverse sector and several finite inverse-chain no-root certificates, rather than a proof of Machine C nonhalting. Agent19's preexisting valuation-four sum-seven predecessor rule and Agent24's generic even-right gate do not directly cover the same target conditions. Compare the four parameter exclusions carefully against all previous independent high filters before claiming independent density or external novelty.

The most valuable next step is a reduction of the surviving infinite low/high *existential* conditions, ideally proving the actual start's behavior through a structural invariant encompassing entire unbounded families. Even after the proposed joint theorem is validated, its two infinite existential alternatives remain; an exact value of BB(6) is nowhere established here.
