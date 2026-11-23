# Machine C: S2 and q-even high-stop pullbacks

**Status:** the S2/q-even original-source pullback modules passed Lean 4.36.0-rc2 CI in run [45161729614](https://github.com/FlareZ123/bb6/actions/runs/45161729614), with no `sorryAx` in the exported theorem profiles. The S3-preserving six-all integration and its strict-nonredundancy proof are added but await the focused original-source run [45163833154](https://github.com/FlareZ123/bb6/actions/runs/45163833154). These are root-unreachability results for two explicit high-stop parameter cylinders. They do not determine BB(6).

## High-stop coordinates

For the Machine C high-stop family, write
\[
K(j,m)=2^{2m+2}(j+3)-(j+3m+5).
\]
The candidate state is \((2j+3,K(j,m))\). The Lean file CSixSeventhS2Pullback.lean proves the subtraction identity needed to reason about this state and pulls two source-certified image exclusions back to congruence classes in \((j,m)\).

## S2 cylinder

Put \(u=(j-319)/512\) when \(j\equiv319\pmod{512}\). The exact pullback is

\[
j\equiv319\pmod{512},\qquad
3m+102921\equiv185j\pmod{131072}
\]

if and only if

\[
j\equiv319\pmod{512},\qquad
m\equiv72746+75264u\pmod{131072}.
\]

On this cylinder, the high-stop identity and \(2^{17}\mid2^{2m+2}\) give

\[
K(j,m)+95232u\equiv43582\pmod{131072}.
\]

Consequently \(K(j,m)=574+1024v\) for some \(v\in\mathbb N\), with

\[
v+93u\equiv42\pmod{128}.
\]

The existing s2_sector_decompose theorem turns this into the exact S2 source image hypotheses, and blank_ne_s2_image proves that the state is unreachable from the blank tape at every time. The parameter cylinder has density \(2^{-26}\) in the integer \((j,m)\)-lattice.

## Complementary q-even cylinder

The complementary source lift has the exact pullback

\[
j\equiv319\pmod{512},\qquad
171m+355585\equiv49j\pmod{1048576}
\]

if and only if

\[
j\equiv319\pmod{512},\qquad
m\equiv531498+337408u\pmod{1048576}.
\]

Here the high-stop identity gives

\[
106j+57K(j,m)\equiv355300\pmod{1048576}.
\]

Thus \(K(j,m)=574+1024v\), and the remaining congruence is

\[
53u+57v\equiv282\pmod{1024}.
\]

This forces \(u+v\equiv2\pmod4\). Setting \(t=(u+v-2)/4\), the proof reconstructs a natural \(z\) with

\[
u=32z-7t-10,\quad v=12+11t-32z,\quad
(2t-z)\bmod8=1.
\]

The existing blank_ne_s2q_even_image theorem then excludes the high-stop state at every time. This cylinder has density \(2^{-29}\).

The two cylinders are disjoint: their induced m-residues differ by \(65536\pmod{131072}\) for every \(u\). Their combined density is \(9\cdot2^{-29}\).

The new `CSixSeventhSixAllS2.lean` proof establishes that both cylinders were admitted by the entire preceding S3-extended high predicate, not merely by the older six-all base. Both imply the common residue lift `m = 7210 + 9728u (mod 16384)`, where `u=(j-319)/512`; hence `(3*m+7*j+14025) mod 16384 = 5120`, so they are disjoint from the earlier S3 exclusion (whose residue is zero). The base residue `j=319 (mod 512), m=42 (mod 512)` also passes the prior C58/all-depth/late-fast/diagonal/m=0/six-sector filters: `m=2 (mod 4)`, `m=10 (mod 32)`, `(j+25)=24 (mod 32)`, and the six-sector normalizer takes no inverse edge. Thus the new cylinders are genuinely additional to S3. The densities above are exact lattice densities, not a measured fraction of previously surviving candidates.

## Formal artifact

CSixSeventhS2Pullback.lean contains:
- both exact parameter-pullback equivalences;
- both all-time high-stop blank-unreachability theorems;
- the q-even (u,v)-to-(t,z) reconstruction;
- CReach corollaries;
- #print axioms checks for the exported theorems.

CSixSeventhSixAllS2.lean adds both congruence exclusions to the existing six-all high predicate and proves blank_halts_iff_six_both_s2q, preserving the exact low branch and fixed-target root test. The exact iff extension is still pending CI acceptance.

The source imports Agent 4's CSixSeventhS2 and CSixSeventhS2QEven modules. The existing `agent4-c-three-ancestry.yml` workflow source-checks the S2/q-even pullback modules. The existing `agent11-c-diagonal-late.yml` workflow now has an opt-in `s2_sixall_only` path that skips independent M0/S31-only extensions while retaining the exact C58/six-all dependency closure needed for this integration. Until run 45163833154 passes, treat the S3-preserving iff and nonredundancy theorem as proof candidates rather than accepted certificates.
