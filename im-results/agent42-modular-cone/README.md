# Agent 42: source-connected modular inverse cones for Machine C

## Current state

The generic inverse-cone checker and its soundness theorem are in **ModularCone.lean**. The original-source adapter is **ModularConeSource.lean**; it connects the abstract parent/forbidden-image laws to the existing Machine C source reachability relation.

The high-stop theorem in **ModularConeHighStop.lean** is accepted by Lean 4.36.0-rc2 CI (run [45355518699](https://github.com/FlareZ123/bb6/actions/runs/45355518699)). It proves that every accepted adaptive modular cylinder excludes the corresponding original-source CReach target, without imposing the previous relative-growth gate. The exact high-branch criterion integration in **ModularConeHighStopCriterion.lean** also passed CI (run [45357876925](https://github.com/FlareZ123/bb6/actions/runs/45357876925)).

A low-stop counterpart is in **ModularConeLowStop.lean**, including a concrete source exclusion. **ModularConeStopsCriterion.lean** adds the low-stop predicate to the exact low/high criterion. The first combined run 45361871162 reached the low/high modules and found only missing `norm_num` tactic imports in the two concrete arithmetic examples; these were replaced by kernel computation (`decide`). The broader `ModularConeFullCriterion.lean` now imports Agent27's full Boolean/phase criterion and Agent20's C70 rectangle exclusions, then conjoins both modular filters. The full-criterion proof had two arithmetic-normalization failures in run 45363035629; the power identity and high-stop equation were repaired. The current source-closure run 45363797397 is validating the repaired file.

## Mathematical setup

For a unified stop parameter pair \((J,m)\), the source target has
\[
x=2J+1,\qquad y=-J-3m-4,
\]
and the stop equation is
\[
k+J+3m+4=2^{2m+2}(J+2).
\]

The modular inverse cone uses the original source parent law and forbidden odd-image law. Its checker follows every parent branch admitted by the source equations; a residue cylinder is excluded only when all compatible inverse paths reach a forbidden image. The adaptive precision is capped at 32 bits.

The unified high index is \(J=j+1\), where \(j\) is the original high-branch index. The high precision is
\[
b_H(J,m)=\min(32,2m+2)\quad(J\ge2),
\]
with the smaller \(2m+1\) precision at \(J=1\). The low family is \(J=0\), with precision \(\min(32,2m+1)\).

## Exact finite census

The fixed eight-bit checker is a predicate on residue pairs modulo 256. The exhaustive BigInt evaluation gives:

| Family | Accepted cylinders | Immediate root exclusions | Recursive exclusions |
| --- | ---: | ---: | ---: |
| High, all \(J,m\bmod256\) | 39,506 / 65,536 | 16,384 | 23,122 |
| Low, all \(m\bmod256\) | 163 / 256 | 64 | 99 |

High accepted-cylinder depth histogram: 0: 16,384; 1: 9,984; 2: 6,568; 3: 4,088; 4: 1,900; 5: 514; 6: 68.

Low accepted-cylinder depth histogram: 0: 64; 1: 48; 2: 26; 3: 14; 4: 8; 5: 3.

For the adaptive cap-32 probe:
- Unified high sample \(J,m\in[1,127]\): 13,484 / 16,129 accepted.
- Outside the previous unified growth gate \(J\le3m+1\), i.e. \(J>3m+1\): 1,945 / 2,583 accepted.
- Original high index \(j\in[1,127]\), with \(J=j+1\): 13,488 / 16,129 accepted; 1,983 / 2,625 are outside the old original-index gate \(j\le3m\).
- Low sample \(m\in[0,1023]\): 883 / 1,024 accepted. Unresolved \(m<100\): 0, 2, 6, 8, 10, 15, 16, 22, 27, 32, 34, 43, 47, 72, 74, 82, 86, 91, 98.

The census is a finite computation, not a theorem asserting the total count. The source-connected Lean theorem proves each accepted cylinder individually.

## Concrete examples

- High unified \(J=21,m=3\): the root residue is \((43,222)\pmod{256}\), not an immediate forbidden image. Nevertheless the source theorem proves \(\neg CReach(43,5854)\). This is outside \(J\le3m+1\).
- Low \(m=11\): the root residue is \((1,219)\pmod{256}\), not an immediate forbidden image. The source theorem proves \(\neg CReach(1,33554395)\).

## Reproducibility and next work

The probe.py script now mirrors the Lean checker with separate recursion-fuel and modulus arguments: each inverse edge decreases recursion fuel by one, while direct and high edges consume one or \(n+2\) modulus bits respectively. It reports the finite census and adaptive sample counts.

Next:
1. Confirm CI run 45361871162 for the combined low/high exact criterion.
2. Compare the modular predicates against existing affine/late filters to identify strict new exclusions, not merely redundant necessary conditions.
3. Analyze the remaining inverse-cone survivor paths, especially cases where the valuation reaches the current precision bound.
4. Keep all experimental code and census data here; reserve results/ for source-certified mathematical statements and their carefully qualified finite enumerations.
