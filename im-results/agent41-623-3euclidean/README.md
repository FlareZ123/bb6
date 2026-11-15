# The #623 root gap as a perturbed 3-Euclidean algorithm

**Status:** intermediate reduction, not a nonhalting proof. This note is a coordinate reformulation of the canonical gap dynamics and identifies the remaining arithmetic obstruction.

## 1. Coordinates

For a positive root-section state \(D(a,d)\), put
\[
q=\min(a,d),\qquad p=|a-d|,\qquad g=p-3q.
\]
This agrees with the existing canonical gap:
- if \(a\ge d\), then \(p=a-d\), \(q=d\), and \(g=a-4d\);
- if \(d>a\), then \(p=d-a\), \(q=a\), and \(g=d-4a\).

Thus the ratio-four boundary is simply \(p=3q\). The root's terminal-window problem is a quantitative non-small-remainder problem for \(p-3q\), with the exact parity offsets from the old-ray formulas retained when applying the existing terminal-window lemmas.

## 2. The ideal projective map is a 3-Euclidean map

Ignoring the exact drain corrections, the two leading updates from `RootGapScaleDynamics.md` become:

- If \(g>0\), equivalently \(p>3q\):
  \[
  (p',q')=(p-3q,\,3q).
  \]
- If \(g<0\), equivalently \(p<3q\):
  \[
  (p',q')=(3q-p,\,p).
  \]

This is a subtract-and-swap Euclidean algorithm with multiplier 3. The quantity \(|p-3q|\) is the remainder at the branch boundary. A small remainder is precisely what can move the next state into the narrow ratio-four terminal window.

The common quadratic form from `GapScaleResidualSource.lean` has a particularly simple expression in these coordinates:
\[
Q(g,q)=g^2+9gq+21q^2
      =p^2+3pq+3q^2.
\]
Both ideal branches have the same exact gain:
\[
Q(p',q')=Q(p,q)+6q^2.
\]
For the first branch this follows by expanding
\[
Q(p-3q,3q)=p^2+3pq+9q^2;
\]
for the second,
\[
Q(3q-p,p)=p^2+3pq+9q^2.
\]

This explains the common quadratic gain geometrically: it is the same identity on both branches of the 3-Euclidean map.

## 3. Exact corrections in these coordinates

Let \(\beta=\mathrm{beta}(B,c,v)\) and \(\delta=\mathrm{delta}(E,m)\) be the source corrections in `GapScaleResidualSource.lean`. With \(g=p-3q\), the exact source updates give:

- If the exact output is on the left side:
  \[
  g'=g-9q+\beta-4\delta,\qquad
  m'=3q+\delta,
  \]
  hence
  \[
  p'=g'+3m'=g+\beta-\delta,\qquad q'=3q+\delta.
  \]
- If the exact output is on the right side:
  \[
  g'=-4g-9q+\delta-4\beta,\qquad
  m'=3q+g+\beta,
  \]
  hence
  \[
  p'=g'+3m'=-g+\delta-\beta,\qquad q'=p+\beta.
  \]

The leading 3-Euclidean updates result when these correction terms are suppressed and the exact output side agrees with the sign of \(g\). The 20,000-state root replay reports no side-selection mismatch after canonical-ray entry, but that remains computational evidence.

The correction terms are structured ternary-drain data, not arbitrary noise. The exact weighted drain identity and first-counter bound are in:
- `im-results/agent22-623-root-ray-20k/ExactDrainCocycleSource.lean`;
- `im-results/agent22-623-root-ray-20k/ExactRayCorrectionRelations.lean`;
- `im-results/agent49-parity623/GapScaleResidualSource.lean`.

## 4. What this does and does not prove

The source-level theorem `quadratic_gap_scale_gain` proves, on the four canonical rays and for successful transitions in the new affine cone,
\[
Q(g',m')\ge Q(g,m)+6m^2.
\]
It does not prove that \(|p-3q|\) is large. At the boundary \(p=3q\), the ideal map still has the exact gain \(+6q^2\); therefore the quadratic Lyapunov inequality is compatible with arbitrarily small remainders. It cannot by itself establish the root's avoidance of the terminal window.

The existing 20,000-step diagnostic in `im-results/agent8-623-inverse/RootGapScaleDynamics.md` reports:
- minimum \(g^2/m=4096/235\), at index 16;
- minimum \(|g|/m\) at index 6899, so no uniform linear-in-\(m\) gap bound is plausible;
- the exact old-ray distance scan has a separate minimum square/scale ratio of about 5.54.

These are finite observations only. A root-wide estimate such as \(g^2\ge C m\), with parity offsets accounted for, would be more than enough for the logarithmic terminal-window comparison, but it remains unproved.

## 5. Research target

Prove a non-small-remainder theorem for the **specific perturbed 3-Euclidean orbit** beginning at \(D(0,7)\). In particular, explain why the ternary-drain corrections prevent
\[
|p_n-3q_n|=O(\log q_n)
\]
at every root-reachable state after the finite entry prefix. The ideal 3-Euclidean map alone is insufficient: its integer dynamics can approach the branch boundary. The missing ingredient must encode the root's history or a strong arithmetic restriction on the ternary digits of the correction terms.

Do not repeat finite root replays or merely reprove the common quadratic gain. The highest-value next step is a symbolic invariant or a counterexample to the proposed square-gap bound.
