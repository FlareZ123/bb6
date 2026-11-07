# Canonical ray cocycle for the pinned #623 section orbit

**Status:** the canonical minimal-ray cocycle and its four original-source transition identities compiled in pinned-source CI run [42377437529](https://github.com/FlareZ123/bb6/actions/runs/42377437529). The arithmetic shift equivalences compiled in run [42375801220](https://github.com/FlareZ123/bb6/actions/runs/42375801220). The source-level composition of the terminal ratio-four windows is being checked separately. This remains an intermediate result, not an all-time nonhalting proof.

## Canonical minimal-budget bases

Write
\[
\tau(k)=\frac{3^k-1}{2}.
\]
For a state \(D(a,d)\) in the four-sector new affine cone, choose the least exponent satisfying the indicated ternary budget.

| Sector | Least exponent | Boundary base | Shift | Output factor |
|---|---|---|---|---:|
| Far-left odd | \(k=\min\{j:d+3\le\tau(j)\}\) | \(D(d+5+k,d)\) | \(t=a-d-5-k\) | 1 |
| Far-left even | \(k=\min\{j:d+2\le\tau(j)\}\) | \(D(d+2+k,d)\) | \(t=a-d-2-k\) | 1 |
| Far-right odd | \(k=\min\{j:a-1\le\tau(2j+5)\}\) | \(D(a,a+1+2k)\) | \(t=(d-a-1)/2-k\) | 2 |
| Far-right even | \(k=\min\{j:a<\tau(2j+3)\}\) | \(D(a,a+2+2k)\) | \(t=(d-a-2)/2-k\) | 2 |

The far-left even base is \(D(d+2+k,d)\) for this least-exponent convention. The alternative \(D(d+3+k,d)\) is a valid nonminimal rebase, with its shift reduced by one.

The four original-source shift theorems imply the same exact cocycle in every sector. If the base transition is
\[
T(D_{\rm base})=D(B,E),
\]
then
\[
T(D_{\rm actual})=D(B+c t,E),
\]
where \(c=1\) on left rays and \(c=2\) on right rays. The source wrapper is [CanonicalRayCocycleSource.lean](CanonicalRayCocycleSource.lean). It also proves that the chosen exponents are least in their respective budget classes. The complete wrapper passed the unmodified-source import step in run 42377437529.

## Terminal ratio-four windows in shift coordinates

The source-derived ratio-four conditions become:

| Sector | Necessary terminal condition |
|---|---|
| Far-left odd | \(\left|t-(3d-5-k)\right|\le K+5n+29\) |
| Far-left even | \(\left|t-(3d-2-k)\right|\le K+5n+20\) |
| Far-right odd | \(\left|2t-(3a-1-2k)\right|\le K+5n+12\) |
| Far-right even | \(\left|2t-(3a-2-2k)\right|\le K+8n+17\) |

Here \(n\) and \(K\) are the least exponents in the corresponding source terminal bounds. The four equivalences are proved in [CanonicalRayCocycleArithmetic.lean](CanonicalRayCocycleArithmetic.lean). The source-level composition of the terminal output balance, root-ray bridge, and integer cancellation is in [TerminalRatio4Source.lean](TerminalRatio4Source.lean).

## Connection to the old-ray distance invariant

For an old-cone ray, write its conventional parameter as \(s\):
- left odd: \(a=2d+9+s\);
- left even: \(a=2d+5+s\);
- right odd: \(d=2a+1+2s\);
- right even: \(d=2a+2+2s\).

The canonical terminal-gap expressions above then simplify exactly to:

| Sector | Canonical terminal gap |
|---|---|
| Far-left odd | \(s-2d+9\) |
| Far-left even | \(s-2d+5\) |
| Far-right odd | \(2(s-a)+1\) |
| Far-right even | \(2(s-a)+2\) |

[CanonicalRayRootDistanceArithmetic.lean](CanonicalRayRootDistanceArithmetic.lean) proves these four identities and the following conditional exclusions, using only Std and Lean 4.36.0-rc2:

- left odd: a root lower bound \(R\le |s-2d|\) excludes a terminal window of width \(W\) if \(W+9<R\);
- left even: \(W+5<R\);
- right odd: a root lower bound \(R\le |s-a|\) excludes the window if \(W+1<2R\);
- right even: \(W+2<2R\).

This connects directly to Agent 8's finite root-ray observation: old right rays appeared to satisfy \((s-a)^2\ge a\), and old left rays appeared to satisfy \((s-2d)^2\ge d\), over the sampled prefix. If those inequalities can be proved for all future root states, one can take \(R\) on the order of the square root of the relevant coordinate and compare it with the logarithmic terminal-window width.

The root-distance inequalities remain empirical. Their all-time proof, and a uniform comparison of the resulting \(R\) with \(W\) when the other coordinate dominates the mass, are still open.

## Finite root audit

The exact-integer mirror was replayed for 10,000 consecutive states from the blank-root section state \(D(0,7)\).

- The states at indices 0, 3, and 8 are outside the new affine cone.
- Every state from index 9 through 9,999 has a canonical ray representation.
- All 9,991 exact affine output translations agree with the direct transition; there are zero mismatches.
- The ratio-four shift window has one candidate in this prefix, at index 13, state \(D(122,438)\). Its canonical ray is far-right even with \(k=2,t=155\), base \(D(122,128)\), base output \(D(4,385)\), and actual output \(D(314,385)\). The latter continues to \(D(74,950)\), so this candidate is explicitly survived.
- The closest excluded state is index 16, \(D(876,235)\), with exact margin 2 outside its window.

The reproducible script is [canonical_ray_terminal_scan.py](canonical_ray_terminal_scan.py); run it from this directory with:

python canonical_ray_terminal_scan.py --steps 10000

This scan is finite computational evidence. The index-13 candidate is not itself a halting result: its actual successor is D(314,385), which continues to D(74,950). The scan has been independently reproduced in the private Python analysis; the committed script is also included in the pending CI workflow. No all-time separation theorem for the genuine root ray shifts has been established.

## Remaining mathematical obstacle

The cocycle reduces the infinite problem to the actual sequence of canonical shifts and their distance from the four terminal targets. The remaining task is to prove a root-specific lower bound on that distance, or to find another invariant that excludes every terminal window after the finite prefix. The general new affine cone is not forward-closed for arbitrary states, so cone membership alone is insufficient.

The exact value of \(BB(6)\) remains undetermined by this work.
