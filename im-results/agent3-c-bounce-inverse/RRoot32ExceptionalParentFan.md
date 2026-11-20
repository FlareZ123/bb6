# Root32 exceptional R(t) branch: complete parent fan and a new exclusion

**Status:** paper-level exact source-parent analysis. It uses the certified complete source grammar in BB6.Agent46.section_preimage_all_iff, plus the existing blank reachability inverse and odd-right image invariants. The new composition has not yet been compiled in one Lean module. It is not a full E7, Machine C, or BB(6) exclusion.

## 1. Exceptional parameterization

The D0E inverse chain reaches

\[
R(t)=(2861931660t+767469219,\;2092249530t+561067594).
\]

The exact root equation is

\[
17300+22155(t+j)=5\cdot2^{E-17},\qquad r=32+64j.
\]

It implies \(t+j\equiv4\pmod{32}\). The even-right inverse is unique for \(t\not\equiv3\pmod4\). On the remaining cylinder write

\[
t=3+4q,\qquad r\equiv96\pmod{256}.
\]

Then \(R_x\) is odd, \(R_y\) is even and at least six, and

\[
S=R_x+R_y=16191080383+19816724760q,
\qquad S\equiv7\pmod8.
\]

Also put

\[
C=R_x+2R_y=23028896567+28185722880q.
\]

## 2. Complete source-parent alternatives for R(t)

Apply section_preimage_all_iff to a putative source edge into \(R(t)\).

- The \(a=0\) recursive branch requires \(8\mid S\), impossible since \(S\equiv7\pmod8\). Its exceptional cases are too small.
- The finite \(a=1,k\le3\) cases are too small.
- The high \(a=1\) branch requires \(S+1=16\cdot2^n\). This is impossible for every t: the original affine formula gives
  \[
  S+1\equiv2\pmod3,\qquad S+1\equiv4\pmod5.
  \]
  The first congruence would force \(n\) odd, while the second would force \(n\equiv2\pmod4\).
- For \(a\ge2\), the low branch is exactly the direct parent
  \[
  R'(t)=(4954181190t+1328536811,\;1046124765t+280533796).
  \]
  Its low-region inequalities hold because \(R_x>0\) and \(R_y\ge6\).
- The high even-\(a\) branch is impossible because it requires S even.
- In the high odd-\(a\) branch, \(y=3\) is impossible. The remaining branch has
  \[
  S+1=2^n(2a+6),\qquad
  2k+a+9+3n=C+2.
  \]
  Since \(a\) is odd, \(2a+6\) is divisible by four. The second equation, with \(C\) odd, forces \(n\) odd. Therefore every such parent has the exact form
  \[
  a=\frac{S+1}{2^{n+1}}-3,\qquad
  k=\frac{C-a-7-3n}{2},
  \]
  where
  \[
  n\text{ is odd},\qquad n\le1+v_2(W(q)),\qquad
  W(q)=2023885048+2477090595q.
  \]
  Here \(S+1=8W(q)\). This is an unbounded-depth family as \(v_2(W(q))\) varies; no finite depth cutoff is justified.

Thus every source parent is either the direct parent \(R'(t)\) or one of the explicitly parameterized odd-\(a\) bounce parents above. There is no \(a=1\) parent.

## 3. Excluding the odd-a branch for q = 3 mod 8

If \(q\equiv3\pmod8\), then q is odd, so \(W(q)\) is odd. Hence \(v_2(S+1)=3\). The odd n bound forces \(n=1\), leaving only

\[
A(q)=
(4047770093+4954181190q,\;
 9490563232+11615770845q).
\]

For \(q\equiv3\pmod4\), the right coordinate of \(A(q)\) is odd and its coordinate sum is

\[
13538333325+16569952035q\equiv2\pmod4.
\]

The source-certified blank_no_odd_sum_two theorem excludes this parent. Therefore no odd-\(a\) bounce parent of \(R(t)\) is blank-reachable when \(q\equiv3\pmod8\).

## 4. Excluding the direct-parent branch for q = 3 mod 8

For \(t=3+4q\), the direct parent is

\[
R'(t)=
(16191080381+19816724760q,\;
 3418908091+4184499060q).
\]

Its coordinates are odd and its sum is

\[
19609988472+24001223820q.
\]

For \(q\equiv3\pmod8\), this sum is \(4\pmod{16}\). The source-certified odd/odd low-valuation reachability equivalence therefore forces its unique parent

\[
P_1(q)=
(9804994234+12000611910q,\;
 6611951161+8092555485q).
\]

Writing \(q=8m+3\),

\[
P_1=
(96004895280m+45806829964,\;
 64740443880m+30889617616).
\]

This is even/even with right coordinate at least six and coordinate sum

\[
160745339160m+76696447580\equiv4\pmod8.
\]

The source-certified even-right inverse forces its direct parent

\[
P_1'=
(160745339160m+76696447578,\;
 32370221940m+15444808807).
\]

The right coordinate of \(P_1'\) is odd and at least five, while

\[
P'_{1,x}+P'_{1,y}
=193115561100m+92141256385
\equiv1\pmod4.
\]

The source-certified blank_no_odd_sum_one theorem excludes \(P_1'\). Hence \(R'(t)\) is also blank-unreachable for \(q\equiv3\pmod8\).

## 5. New infinite subfamily exclusion and root-index translation

The complete parent fan in Section 2 has only the two alternatives treated in Sections 3 and 4. Consequently,

\[
\boxed{q\equiv3\pmod8\Longrightarrow\neg CReach(R(3+4q)).}
\]

Equivalently, writing \(q=8m+3\), this excludes \(R(t)\) for

\[
t=32m+15\equiv15\pmod{32}.
\]

The exact root equation gives \(t+j\equiv4\pmod{32}\), so

\[
j\equiv21\pmod{32},\qquad
\boxed{r=32+64j\equiv1376\pmod{2048}.}
\]

The D0E chain has source edges D0E \(\to\) E7 \(\to\) P \(\to\) R, after its already-excluded direct fork. Thus the new R exclusion removes the D0E/E7 branch on the root-index cylinder \(r\equiv1376\pmod{2048}\).

**Important limitation:** the high-stop target T was previously reduced to D0E(t) reachable or L(t) reachable. This result removes only the D0E alternative on the stated cylinder; it does not by itself exclude T, because L(t) remains a separate possible branch. On this same cylinder, the L analysis reduces its surviving P0 path through A0 and Q to

\[
Q'=(151002951960m+72048060928,\;
    37241215540m+17769002135),
\]

an even/odd sum-three-mod-four target. That is the next concrete L-side target, not an excluded state.

## Verification boundary and next work

The parent classification is a direct case split of the unbounded original-source grammar. The q=3 mod8 exclusion is an exact composition of that fan with existing source-certified inverse and blank-image theorems. The new composition still needs a Lean 4.36.0-rc2 wrapper and axiom audit.

Next targets:
1. Formalize the two-branch R parent classification and the q=3 mod8 exclusion.
2. Continue the q≡7 mod8 direct-parent branch, where R' reduces to an even/even sum-zero target.
3. Continue the q even odd-a bounce family with odd depths \(n\le1+v_2(W(q))\); this depth is not uniformly bounded.
4. On \(r\equiv1376\pmod{2048}\), attack the remaining L-side Q' family rather than claiming the high-stop target is closed.

Keep this work in im-results/. Do not promote it to results/ until the composed source theorem is compiled and independently reviewed.
