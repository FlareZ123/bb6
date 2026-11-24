# Agent 42: source-connected modular inverse cones for Machine C

## Current state

The generic inverse-cone checker and its soundness theorem are in **ModularCone.lean**. The original-source adapter is **ModularConeSource.lean**; it connects the abstract parent/forbidden-image laws to the existing Machine C source reachability relation.

The high-stop theorem in **ModularConeHighStop.lean** is accepted by Lean 4.36.0-rc2 CI (run [45355518699](https://github.com/FlareZ123/bb6/actions/runs/45355518699)). It proves that every accepted adaptive modular cylinder excludes the corresponding original-source CReach target, without imposing the previous relative-growth gate. The exact high-branch criterion integration in **ModularConeHighStopCriterion.lean** also passed CI (run [45357876925](https://github.com/FlareZ123/bb6/actions/runs/45357876925)).

A low-stop counterpart is in **ModularConeLowStop.lean**, including a concrete source exclusion. **ModularConeStopsCriterion.lean** adds the low-stop predicate to the exact low/high criterion. The first combined run 45361871162 reached the low/high modules and found only missing `norm_num` tactic imports in the two concrete arithmetic examples; these were replaced by kernel computation (`decide`). The broader `ModularConeFullCriterion.lean` now imports Agent27's full Boolean/phase criterion and Agent20's C70 rectangle exclusions, then conjoins both modular filters. The low-stop theorem and concrete example passed dedicated Lean CI run 45364029622. The full-criterion run 45363797397 exposed one remaining power-successor normalization issue; it was replaced with an explicit Nat.pow_succ identity. The repaired full Boolean/C70/modular criterion passed source-closure CI [45364535182](https://github.com/FlareZ123/bb6/actions/runs/45364535182).

## Exact-target height precision and fixed-depth rays

The earlier adaptive filter used only the precision supplied by the stopping exponent. The exact right coordinate k permits any b satisfying 3*2^b <= k+2, regardless of m. **HeightCone.lean** takes b=min(cap, floor(log2((k+2)/3))) and runs the same certified checker on the actual (x,k). It proves soundness relative to the existing modular exclusion theorem. For a fixed m, any accepted base J0,k0 at precision b excludes every upward ray target

- J=J0+2^b*t;
- k=k0+(2^(2m+2)-1)*2^b*t.

The targets obey the same stopping equation when the base does. Both coordinates remain congruent and the right-size bound only increases. In particular m=0, J=12+8*t has targets (25+16*t,40+24*t). The b=3 base certificate reduces to true; the earlier adaptive high filter (b=2) reduces to false for **every** member of this infinite ray. This establishes strict extension of the old modular filter, not necessarily of all other independent parameter sieves.

The arithmetic proof bodies, including the old-filter failure on the entire ray, passed local Lean 4.36.0-rc2 against an exact copy of the checker definitions with the existing exclusion-soundness theorem supplied as a hypothesis. A source-connected wrapper and the combined exact criterion **HeightConeCriterion.lean** are now submitted for the existing manual source-closure workflow. Until that run is accepted, the new source wrapper is unverified. The exact predicate conjoins the height filter with the previously accepted full criterion; the unbounded root decision remains open.

In the finite J=1..16384 sample, m=0: old 4095, height 11515, additional 7420; m=1: old 5120, height 11644, additional 6524; m=2: old 9728, height 12480, additional 2752. No old accepted point is lost in these samples (not yet a monotonicity theorem). The source integration preserves all old exclusions by conjunction regardless.

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
1. Compile HeightConeCriterion using the existing source-closure workflow. Its diagnostic tests strictness against the earlier full Boolean/C70/modular parameter filters.
2. If the strictness witness is nonempty, kernel-check a concrete witness using the source-equivalent fast Boolean predicate and investigate the remaining inverse branches.
3. Investigate unbounded precision and exact-target survivor paths, especially the pure-power valuation branch. Keep empirical counts distinct from source-machine decisions.
