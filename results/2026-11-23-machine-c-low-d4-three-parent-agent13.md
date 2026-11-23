# A three-parent valuation-six source exclusion for Machine C: a new low-stop cylinder

**Agent 13 · 23 November 2026 · original-source Lean 4.36.0-rc2 proof.**

## Main result

For every \(z\ge0\) satisfying \(z\equiv65\pmod{512}\), put
\[
m=512z+67,\qquad K_m=2^{2m+3}-(3m+4).
\]
Then the exact blank-origin Machine C section orbit **never reaches** \((1,K_m)\), at any time. This is a new infinite necessary-low-stopping-parameter exclusion, independent of the 16/128 classes proved by the [two-parent source theorem](2026-11-23-machine-c-low-source-sixteen-agent13.md). Together, the two disjoint results exclude \(64+1=65\) residue classes modulo 512 of \(z\) in the fixed \(m=512z+67\) family. This ratio is **not** a fraction of all six-state machines or of actual halts.

The Lean source is [`LowM67D4Source.lean`](../im-results/agent13-residual-frontier/LowM67D4Source.lean), containing the formally checked theorem `BB6.Agent13D4Low.low_stop_m67_z65_mod512_unreachable`. The original-source proof compiled in [GitHub Actions run 45248524167](https://github.com/FlareZ123/bb6/actions/runs/45248524167); its 61-module Lean 4.36.0-rc2 closure printed exactly `[propext, Classical.choice, Quot.sound]` as the theorem's axiom profile, with no `sorryAx`.

## Source-exact proof

Every low target with \(m=512z+67\) has the form \(K_m=256u+51\), where \(u=2^{2m-5}-6z-1\). The same four universal exact source inverse steps from the two-parent result yield the section target \(R_u=(180u+28,166u+25)\).

Under \(z\equiv65\pmod{512}\), exponent arithmetic gives \(u\equiv633\pmod{1024}\). Write \(u=1024t+633\), \(t\ge0\). Then, with \(R_u=(x,y)\),
\[
x+y+1=354304t+219072\equiv64\pmod{128}.
\]
Thus the complete original-source predecessor grammar admits **exactly three candidate bounce depths**, \(n\in\{0,2,4\}\). More precisely, every actual incoming predecessor belongs to this three-member list; candidate membership alone does not assert a transition exists. The full, *unbounded*, source-derived fan classification is separately kernel-checked in [`EvenOddValuationSix.lean`](../im-results/agent13-residual-frontier/EvenOddValuationSix.lean), GitHub Actions [45248128114](https://github.com/FlareZ123/bb6/actions/runs/45248128114).

The exact candidate parent coordinates and forced subsequent inverse paths are:

| Inverse depth | Candidate parent \((a_n,k_n)\) | Source-exact forced inverse path | Terminal odd-right image obstruction |
|---|---|---|---|
| \(n=0\) | \((177152t+109533,\ 173568t+107317)\) | none | right odd \(\ge5\), sum \(2\bmod4\) |
| \(n=2\) | \((44288t+27381,\ 240000t+148390)\) | even-right B, even-right B, affine A | \((464288t+287055,\ 30000t+18547)\), sum \(2\bmod4\) |
| \(n=4\) | \((11072t+6843,\ 256608t+158656)\) | even-right B, odd/odd O | \((197992t+122410,\ 163148t+100867)\), sum \(1\bmod4\) |

For both nonempty paths, the exact side conditions of each original-section inverse theorem are established by linear arithmetic uniformly for all \(t\). In particular, the putative final state has odd right counter at least five and total coordinate sum \(1\) or \(2\pmod4\), which violates the original blank-section odd-image invariant (only residues 0 or 3 are possible for such a state). Hence **all** original-section incoming parents of \(R_u\) are blank-unreachable, so \(R_u\) itself is blank-unreachable by the complete inverse grammar and the fact its left counter exceeds five. The initial four inverse equivalences then rule out the stopping target \((1,K_m)\).

## Relation to the main research objective

This proves a genuinely additional infinite residue class requiring a **three-parent** rather than two-parent classification. It extends the complete original-source low-stopping obstruction from 64/512 to **65/512** of the studied \(m\equiv67\pmod{512}\) parameter ray. It does **not** decide Machine C's halting or nonhalting, and it gives neither an upper bound for all six-state machines nor an exact value for BB(6).

The downstream [`LowM67SeventeenCriterion.lean`](../im-results/agent13-residual-frontier/LowM67SeventeenCriterion.lean) is **also kernel-accepted** in [CI 45248949584](https://github.com/FlareZ123/bb6/actions/runs/45248949584): 245 project modules, no `sorryAx`, axiom profile `[propext, Classical.choice, Quot.sound]`. The exact source-blank halting equivalence `BB6.Agent13Low17Joint.blank_halts_iff_six_low17` losslessly adds the new modular exclusion \(m\not\equiv33347\pmod{262144}\) on top of the five previous necessary low-stop restrictions. Its two quantified low/high residual branches remain unbounded.

The [single combined original-source theorem](../im-results/agent13-residual-frontier/LowM67All65Source.lean), `BB6.Agent13Low65Source.low_stop_sixtyfive_mod512_unreachable`, is itself kernel accepted in [CI 45249448433](https://github.com/FlareZ123/bb6/actions/runs/45249448433): 67 source modules, standard axioms and no `sorryAx`. It states all 65/512 parameter exclusions under the same `m=512z+67` and low stop identity.
