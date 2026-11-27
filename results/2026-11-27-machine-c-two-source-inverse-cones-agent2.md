# Two independent source-certified missing-image cones for Machine C

**Agent 2, 27 November 2026.** Machine C is the six-state two-symbol candidate with unchanged accelerated first-return map `F = BB6.Agent46.secNext`; its authentic blank-derived section starts at `(5,1)`. The source-backed results below establish two new positive-density forbidden-image classes and infinite necessary-halting-parameter exclusions. **Neither Machine C halting nor BB(6) is decided.**

## Theorems

**Strict first-to-second image gap.** For every natural (x,y,t), writing (S=x+y),

[
x\equiv5\pmod8,\quad y\equiv3\pmod8,\quad
S\equiv48\pmod{64},\quad y\ge8
\quad\implies\quad
\mathrm{run}(F,t,\mathrm{some}(5,1))\ne\mathrm{some}(x,y).
]

This source-excluded cylinder has ambient natural density **1/512**. A separate constructive original-source theorem proves that **every target actually has one genuine incoming section edge, while none has two**: it lies in the strict image stratum (I_1\\setminus I_2). The explicit parent is `a=(x+y-4)/2, k=(x+3*y-10)/4`; the unchanged section inverse certifies the depth-zero even-bounce edge. Source [FirstImageStrictSource.lean](../im-results/agent2-c-oddodd-cone/FirstImageStrictSource.lean), original-source Lean [CI 45921780574, SUCCESS](https://github.com/FlareZ123/bb6/actions/runs/45921780574). The theorem eliminates all original-source direct, exceptional (a=0,1), and high-bounce predecessor branches, uniformly in the recursion depth. Every possible predecessor ((a,k)) would have (k\ge5), (k\equiv1\pmod2), (a+k\equiv1\pmod4). This contradicts the original `BB6.Agent3.section_odd_image` image invariant, which forces the sum of any actual output with odd right coordinate at least five to be (0) or (3\pmod4). The actual seed ((5,1)) is outside the cylinder. Source theorem `BB6.Agent2COddOddCone.blank_unreachable` in [OddOddConeSource.lean](../im-results/agent2-c-oddodd-cone/OddOddConeSource.lean); unchanged-source Lean [CI 45919216509, SUCCESS](https://github.com/FlareZ123/bb6/actions/runs/45919216509).

**Strict second-to-third image gap.** If

[
y\ge5,\qquad S\equiv4\pmod{16},\qquad
3S+2y\equiv206\pmod{256},
]

then the target ((x,y)) has **two consecutive genuine original section predecessors from some source, but never three**. It belongs to (I_2\setminus I_3) where (I_n) denotes the set of states with (n) successful consecutive (F)-predecessors; hence it is excluded from the authentic blank orbit at every time. This cylinder has ambient natural density **1/2048**, and is disjoint from Agent 34's earlier strict odd-third-image cylinders with ((S\bmod16,(3S+2y)\bmod128)=(4,114)) and ((12,46)), since the present residues are ((4,78)).

The unique first-parent equations in the original section yield (S=2a+4) and (x+3y=4k+10), hence **(a\equiv0\pmod8), (a+k+1\equiv48\pmod{64})**. Every possible second predecessor ((b,\ell)) of such a parent ((a,k)) must have (\ell\ge5), odd (\ell), and (b+\ell\equiv2\pmod4), again contradicting the universal original-source odd-image invariant. In the odd high-bounce inverse equation (a+k+1=2^n(2(b-1)+8)), the valuation forces (n<3), parity and cost prohibit (n=1), and (n=0,2) give the required forbidden residue. Exceptional and direct/even-high-bounce inverse cases are exhausted by the original grammar. The proof is fully quantified, without cutoff.

The genuine two-edge chain is constructed uniformly:
[
a=(S-4)/2,\quad k=(x+3y-10)/4,\quad
b=(a+k-5)/2,\quad \ell=(a+3k-9)/4.
]
The target conditions imply natural integrality, the original input guards, and both exact cost equations, so the unchanged `complete_section_inverse` theorem proves `F(b,ℓ)=some(a,k)` and the unchanged `oddodd_parent_iff` proves `F(a,k)=some(x,y)`. The [broad source theorem](../im-results/agent2-c-oddodd-cone/ThirdImageBroadConeSource.lean) has accepted original-source [CI 45921111379, SUCCESS](https://github.com/FlareZ123/bb6/actions/runs/45921111379). The [constructive (I_2\setminus I_3) theorem](../im-results/agent2-c-oddodd-cone/ThirdImageBroadTwoEdges.lean) is compiled in the associated [strictness audit](../im-results/agent2-c-oddodd-cone/ThirdImageBroadStrictness.lean); consult the latest successful complete workflow run before claiming the compounded proof has passed.

## New infinite stopping families

The original necessary **high** stopping equation is
[
k+j+3m+5=2^{2m+2}(j+3),
\qquad (x,y)=(2j+3,k).
]
Algebraic substitution into the two source cones gives these two excluded parameter lattices, each with arbitrary unbounded (j,m):

* **First cone:** (m\ge5, m\equiv1\pmod4, j\equiv3m+50\pmod{64}), high parameter density **1/256**. Concrete example ((j,m,k)=(1,5,16363)), target ((5,16363)).
* **Third-image cone:** (m\ge6, m\equiv2\pmod4, j\equiv15m+222\pmod{256}), high parameter density **1/1024**. Concrete example ((j,m,k)=(56,6,966577)), target ((115,966577)).

Their congruences on (m\bmod4) are disjoint. Combined, they eliminate a **5/1024** natural-density fraction of the entire two-dimensional *necessary high-stopping parameter lattice*. This proportion is **not a probability of settling randomly chosen six-state machines** and is not a global halting proof. The densities are paper-level exact congruence counts rather than separate Lean formalizations.

For both source cones, the previous **fully recursive six-sector forced-inverse filter** `BB6.Agent11SixForced.sixForcedExcluded` returns **false**: the normalizer fixes each target in the first cone, and strips just the first genuine inverse in the third-image cone before stopping at the source-forbidden parent. Thus the new theorems add information unavailable from that particular preexisting fixed-target exclusion Boolean. They need not be logically independent of every other arithmetic or quotient filter in the repository. The first-cone strictness source audit [CI 45920107435, SUCCESS](https://github.com/FlareZ123/bb6/actions/runs/45920107435) checked this exact claim.

The [first-source lossless halting criterion](../im-results/agent2-c-oddodd-cone/OddOddHighIntegration.lean) is accepted in [CI 45919935795](https://github.com/FlareZ123/bb6/actions/runs/45919935795). Its [combined two-cone refinement](../im-results/agent2-c-oddodd-cone/BroadTwoConeHaltingCriterion.lean), **kernel-accepted in [CI 45921234582](https://github.com/FlareZ123/bb6/actions/runs/45921234582)**, retains the original low stopping branch and adds both high-parameter exclusions to `BB6.Agent11SixAll.blank_halts_iff_six_both` without changing either original exact root decider. As always, these are **lossless reductions of still-unbounded existential quantifiers**, not decisions.

## Reproducibility and open boundary

The original exact section map, exceptional branches, all-depth predecessor iff, actual blank root, and source image invariant remain unchanged. The proof modules and manual Lean 4.36.0-rc2 target are under [im-results/agent2-c-oddodd-cone](../im-results/agent2-c-oddodd-cone/) and the existing [source-audit workflow](../.github/workflows/agent13-m16-high-family-interface.yml). The kernel-accepted principal theorems have only the usual Lean logical axioms `propext`, `Quot.sound`, and where needed `Classical.choice`; none depends on `sorryAx`. Independently accepted source results include the original [full inverse grammar](../im-results/agent3-c-bounce-inverse/FullSectionInverse.lean), the [odd/odd unique inverse](../im-results/agent3-c-bounce-inverse/OddOddWedge.lean), and the original [one-step image theorem](../im-results/agent3-c-odd-image/Agent3CImage.lean).

What is *still missing* is closure of the remaining unbounded low and high blank-root stopping parameters, or an explicit authentic terminal witness. These new infinite exclusions alone cannot determine Machine C halting or the exact six-state Busy Beaver value.
