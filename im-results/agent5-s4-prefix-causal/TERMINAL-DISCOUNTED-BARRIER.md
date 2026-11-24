# Terminal obstruction from discounted moments and nested suffix barriers

**Status:** intermediate mathematical development. This is not a proof that the S4 trajectory is nonhalting, and it does not determine BB(6). It gives a finite-mass halting criterion and a compressed route for constructing the required root-connected invariants.

## 1. Gate-local half-discount contraction

Write a stack as coefficients (x_i=b_i+1\ge 1), with
\[
M=\sum_i x_i,\qquad P(z)=\sum_i x_i z^i,\qquad W=\sum_i x_i2^i.
\]
For a successful S4 gate with offset (c\), let (r) be the carry depth and (m) the final odd carry. The exact carry identities are
\[
(2-z)\sum_{i=0}^{r}t_i z^i
=2(P_{\le r}(z)+c)-m z^{r+1},
\]
and
\[
P_{U}(z)-P_{S}(z)
=c+\frac{z-1}{2}\sum_{i=0}^{r}t_i z^i
+\frac{5z^r-z^{r+1}}2.
\]
Using (P_{>r}(z)\le Mz^{r+1}), (m\le M+c), and (z^r\le1), one obtains, for (0<z<1),
\[
P_U(z)\le aP_S(z)+\beta M+\gamma c+\delta,
\]
where
\[
a=\frac1{2-z},\quad
\beta=\frac{3z(1-z)}{2(2-z)},\quad
\gamma=\frac{2+z-z^2}{2(2-z)},\quad
\delta=\frac{5-z}{2}.
\]
Since (M_U=M_S+c+2), centering at \(\alpha=\beta/(1-a)=3z/2\) gives the compact recurrence
\[
R_U(z)\le \frac1{2-z}R_S(z)
+\frac{(1-2z)c+5-7z}{2},
\qquad R(z)=P(z)-\frac{3z}{2}M.
\]

At (z=1/2), the offset disappears:
\[
\boxed{R_U\le\frac23R_S+\frac34},
\qquad R=P(1/2)-\frac34M.
\]
Consequently, after (g) successful suffix gates,
\[
R_g\le\left(\frac23\right)^gR_0
+\frac94\left(1-\left(\frac23\right)^g\right).
\]
A final head bump of size (d\) adds (d/4) to (R). This contraction is universal: it does not require a bound on the gate offset or carry depth.

This is useful after a prefix-return factorization. The shallow original gates change only the tracked prefix; the induced suffix word consists of effective S4 gates and a possible pending head bump. The suffix potential is then contracted by the number of effective gates, without replaying every shallow original gate.

## 2. A finite-mass terminal-halting criterion

For a stack of length (L\), Jensen gives
\[
\frac{P(z)}M
=\sum_i\frac{x_i}{M}z^i
\ge \left(\sum_i\frac{x_i}{M}2^i\right)^{\log_2 z}
=\left(\frac WM\right)^{\log_2 z}.
\]
Because (W\le 2^{L-1}M\) and (0<z<1),
\[
\boxed{P(z)\ge Mz^{L-1}.}
\]

A halting gate requires (W+c=2^r). Suppose a root-connected invariant at the relevant suffix depth has established
\[
P(z)\le \frac32z^L M+C(z).
\]
Then halting is impossible whenever
\[
\boxed{Mz^{L-1}\left(1-\frac32z\right)>C(z).}
\]
In particular, at (z=1/2), the sufficient condition is
\[
\boxed{M>2^{L+1}C(1/2).}
\]

For a fixed constant (C), the geometric factor (z^{L-1}(1-3z/2)) is maximized at (z=2(L-1)/(3L)), with maximum (L^{-1}(2(L-1)/(3L))^{L-1}). In an actual application (C=C(z)), so the true optimization must include the (z)-dependence of the invariant constant.

The criterion also applies **after stripping a fixed prefix**. By the exact boundary-word factorization, a gate that crosses a tracked prefix induces a gate on the remaining suffix with an effective offset. If the original gate halts, that induced suffix gate must satisfy the same power-of-two condition. Thus it is enough to establish the discounted invariant on the active suffix, not necessarily on the entire stack at once.

## 3. Macro-prefix barrier lemma

Let a finite macro word (B) act on an active suffix, and track its first (L) coefficients. The projected prefix map is obtained by applying the exact truncated carry rule to each effective gate, including any pending head bump.

Suppose the projected prefix has a finite preperiod followed by a cycle. Scan every effective gate in every phase of that transient-plus-cycle. If every carry depth is **strictly less than (L)**, then no gate in any future macro block touches the suffix beyond those (L) coefficients. The tracked prefix repeats, the remaining tail is unchanged, and no future gate can consume the full stack.

If a carry depth reaches (L), this is not a failure of the method: it identifies the next boundary gate. Extract its induced suffix word and repeat the construction one level deeper.

This gives a concrete finite certificate target: a root-connected macro word, a prefix cycle, and a strict carry-depth bound. It is stronger than merely observing that a long finite simulation contains no halting event.

## 4. Current S4 continuation

The existing hierarchy in `s4_nested_depth6.mjs` supplies the Q/R/V/W/X/Y/Z/F return words. The next attempted extension is the induced word
\[
G=F^{1280},
\]
which corresponds to 25,600 Y blocks. The outer ten-digit prefix is already fixed by the Z/F hierarchy; G is extracted using F's five-digit prefix and acts on the suffix after the first fifteen digits.

The current experiment searches for a cycle of the next fifteen-digit suffix prefix under G, then scans the carry depth of every G gate across the complete transient and cycle:

- If the maximum depth is below 15, this yields a 30-digit barrier and a conditional nonhalting proof for the source-connected trajectory.
- If the maximum depth reaches 15, the witnesses identify the gates from which to extract the next suffix word.

The first implementation mistakenly passed the full fifteen-digit prefix to the F-level extractor; that was corrected to use `F1Tail.slice(0, 5)`. The CI pipeline now uses `set -o pipefail` and preserves the exact JSON output, so a failed computation cannot be mistaken for a successful run with an empty artifact.

### First carry-depth census and G extraction (2026-11-24)

The first compressed census is preserved in `im-results/agent5-s4-nested-depth6/g-level-run.json`. All Q/R/V/W/X/Y/Z/F/G mass identities reported by the script are true. The new induced word has:

- (G=F^{1280}), i.e. 25,600 Y blocks;
- 3,605,465 effective suffix gates;
- zero final pending head addition;
- exact mass identity.

The first fifteen-digit residual prefix is **not fixed after one G block**. This only rejects period one; it is not a negative result about eventual periodicity. The next run searches a bounded 16-block transient-plus-cycle window.

The cheaper carry-depth scans of the already-known V/W/X cycles found no barrier:

| Macro | Tracked digits | Preperiod + period | Maximum carry depth | First boundary witness |
|---|---:|---:|---:|---|
| V | 8 | 65 | 8 | phase 0, gate 152, offset 9,873,943,417,132 |
| W | 7 | 641 | 7 | phase 0, gate 172, offset 1,867,506,164,787,075 |
| X | 8 | 129 | 8 | phase 0, gate 38, offset 777,213,453,706,679,331 |

These witnesses are the next boundary gates, not halting witnesses. The strict-barrier condition fails at each of these three levels, so the hierarchy must continue into the next suffix.

## 5. Proof obligations still open

1. Obtain and inspect the G-level cycle/carry-depth result.
2. If no barrier appears, continue the induced-word construction at the next suffix depth rather than extending a blind full-stack scan.
3. Connect the finite macro factorizations to the source gate semantics using the general boundary-word theorem in `S4BoundaryWord.lean`.
4. Formalize the gate-local contraction and Jensen terminal criterion in Lean.
5. Do not promote this note to `results/` until a root-connected barrier or another independently publishable theorem is actually established.
