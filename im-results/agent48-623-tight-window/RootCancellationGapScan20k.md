# Branch-specific cancellation-gap scan for the authentic D(0,7) root

**Status:** finite computational diagnostic only; no all-time invariant is proved here.

The canonical gap/scale recurrence has the exact forms

- left branch: \(g' = (g-9m)+e_L\), where \(e_L=\beta-4\delta\);
- right branch: \(g' = (-4g-9m)+e_R\), where \(e_R=\delta-4\beta\).

Here \(m=\min(a,d)\), \(g=a-4d\) when \(a\ge d\), and \(g=d-4a\) when \(a<d\). The branch is L for \(g>0\), R otherwise. The leading terms vanish at the two projective cancellation centres \(g/m=9\) and \(g/m=-9/4\).

I ran 20,000 exact high-level transitions from \(D_0=(0,7)\), measuring from index 16 onward. For scale comparison, define \(\ell\) as the least integer with \(3^\ell>2m+1\). The exact correction is computed from the actual next root state, not fitted.

## Finite extrema

| Quantity | Left branch | Right branch |
|---|---:|---:|
| Minimum leading-gap square divided by current scale, \(c^2/m\) | \(123904/49\approx2528.65\), at index 25 | \(315218/689\approx457.50\), at index 22 |
| Maximum \(|e|/\ell\) | \(111/6=18.5\), at index 19 | \(66/6=11\), at index 16 |
| Minimum \(|c|/\ell\) | \(562/5=112.4\), at index 18 | \(794/8=99.25\), at index 22 |
| Minimum \((|c|-|e|)^2/m'\) | \(242064/329\approx735.76\), at index 18 | \(142884/307\approx465.42\), at index 22 |

The two smallest leading-gap witnesses are:

- L, index 25: source \(D(784,8784)\), \(m=784\), \(g=5648\), \(c=-1408\), \(e=-78\), and target \(g'=-1486\), \(m'=2371\).
- R, index 22: source \(D(2610,1378)\), \(m=1378\), \(g=-2902\), \(c=-794\), \(e=38\), and target \(g'=-756\), \(m'=1228\).

The minimum guaranteed-next-gap witnesses are:

- L, index 18: source \(D(104,1914)\), \(c=562\), \(e=-70\), so \(|g'|=492\) and \(m'=329\).
- R, index 22: \(c=-794\), \(e=38\), so \(|g'|=756\) and \(m'=1228\).

The script uses exact integer cross-multiplication when selecting minima/maxima. Its output includes the exact numerator and denominator, not floating-point comparisons.

## Interpretation and next proof obligation

This scan suggests that the root trajectory stays far from the two cancellation centres at the scale relevant to the logarithmic drain correction: even the minimum observed \(|c|/\ell\) is above 99 after index 16, while the largest observed \(|e|/\ell\) is 18.5. The resulting next-gap lower bounds are much stronger than the \(g'^2\ge5m'\) threshold used by the terminal-window bridge.

This is not an induction. Arbitrary states can approach either cancellation centre, and the existing source-level quadratic Lyapunov theorem does not by itself exclude that for the particular root. The missing theorem is a **root-history invariant** controlling the active cancellation form \(g-9m\) or \(-4g-9m\), strong enough to dominate the exact drain correction for all future transitions.

Reproduction: run `node im-results/agent48-623-tight-window/RootCancellationGapScan20k.js` from the repository root. The recurrence and all comparisons are integer-exact.
