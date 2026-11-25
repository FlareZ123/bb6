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


## 6. Exact 3-adic digit normal form for the drain

The previous section left the ternary-drain correction terms opaque. They admit a fully nonrecursive digit description.

For a drain counter \(b>0\), put \(v=\nu_3(2b-1)\), write
\[
(2b-1)/3^v=6b^++1+4\epsilon,\qquad \epsilon\in\{0,1\},
\]
and define \(b^+=((2b-1)/3^v-1-4\epsilon)/6\). The unchanged source evaluator consumes the \(v\) low-order ternary digits equal to 1, followed by digit 0 or 2. Its exact output is
\[
\operatorname{evalA}(a,b-1,m)=
(a-v-1+2\epsilon,\ b^+,\ m+(6b^++1+4\epsilon)\tau(v)+2v+2(1-\epsilon)).
\]

Iterating gives a deterministic descent \(b=b_0>b_1>\cdots>b_r=0\). Define the signed cost \(D=\sum_{i<r}(v_i+1-2\epsilon_i)\) and length \(r\). The whole source drain is exactly
\[
\operatorname{drainB}(a,b,d)=(a-D,\ d+3b+2D+2r)
\]
whenever the source ternary budget guarantees success.

Even this valuation recursion can be eliminated. Let \(L\) be the unique integer satisfying
\[
L\equiv b\pmod2,\qquad 3^{L-1}\le2b-1<3^{L+1},
\]
and define
\[
N=(2b-1+3^L)/4.
\]
The valuation expansion proves that \(N\)'s ordinary ternary digits are exactly the coefficients \(1+\epsilon_i\) at distinct positions. Let \(e\) count its ternary digits equal to 2, and let \(\Delta\) be the number of digits equal to 1 minus the number equal to 2. Then
\[
D=L-2e,\qquad r-2e=\Delta,
\]
and the drain has the closed form
\[
\boxed{\operatorname{drainB}(a,b,d)
=(a-L+2e,\ d+3b+2L+2\Delta).}
\]

Consequently the four canonical-ray residuals \((\beta,\delta)\) from **GapScaleResidualSource.lean** are:

| Input ray | \(\beta\) | \(\delta\) |
|---|---:|---:|
| left odd | \(-L+2e-5\) | \(2L+2\Delta+14\) |
| left even | \(-L+2e-2\) | \(2L+2\Delta+8\) |
| right odd | \(4-L+2e\) | \(2L+2\Delta\) |
| right even | \(1-L+2e\) | \(2L+2\Delta+3\) |

Substitution gives the exact eight-case affine gap/scale cocycle in \((g,m,L,e,\Delta)\), tabulated in [DrainValuationNormalForm.md](DrainValuationNormalForm.md). This is a concrete finite-memory extension of the projective state: the correction is now determined by three ordinary ternary digit statistics of a single explicit integer \(N\).

The one-call Lean lemma is drafted in **DrainValuationNormalForm.lean**; it has not yet passed CI or an axiom audit. The whole-drain normal form and the eight-case cocycle are mathematically derived here, with finite BigInt checks as debugging evidence only. The remaining blank-root obligation is to control the actual root's digit-statistic sequence strongly enough to exclude every logarithmic terminal window. This does not prove nonhalting or solve BB(6).


## 7. Monotone mass indexing for the moving 3-adic window

The exact cocycle also gives a useful control on the moving-window boundaries. Replacing the smaller-counter depth by a depth indexed by total mass (S=a+d) makes the depth increase by only 0 or 1 per successful transition. Consequently, the carry-window lower exponent (k) advances by at most 1 and the upper exponent (j) by at most 3. The next middle interval contains the previous output interval after trimming only one low digit; no high-end trim is required. The derivation and its precise source-verification boundary are in [MonotoneMassWindow.md](MonotoneMassWindow.md). This controls window motion, but does not yet prove nonmonochromatic output or close the authentic-root invariant.

## 8. Complete exact drain profiles (24 November)

[DrainProfiles.md](DrainProfiles.md) gives a source-verified, exact all-input MSB ternary fold for the full return map and its sharp per-block affine threshold, with no survival-budget assumption. [FatalSpectrumRegisters.md](FatalSpectrumRegisters.md) is the simpler complete failure-mask fold. Both original-source adapters passed focused CI 45467805135. The all-time blank-root closure is still open; use these exact gates in place of sufficient-budget approximations.

### Direct drain image and excluded rows (Agent41)

[DrainImageDecoder.md](DrainImageDecoder.md): exact standalone Lean inverse for the positive-budget block image, minimum-gap classification, and growing same-parity gaps. The original-source vertical-ray chain (`DrainImageSource`, `ExactParentRays`, `DrainImageAP`, `FatalBandSource`) compiled in CI 45526310656. The stronger finite positive-density count is kernel-checked locally; its `DrainImageDensity`/`FatalDensitySource` source step was added after that run and awaits the current-main audited decoder target.
