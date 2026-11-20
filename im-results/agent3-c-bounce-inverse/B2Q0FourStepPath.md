# B2-to-U5 q=0 path: exact parameter match and inverse-parent obstruction

**Status: intermediate source-orbit reduction, not a Machine C nonhalting proof.** The same-parameter forward path and q=0 residual parameter bridge are explicit. The reverse source-parent analysis reduces T(u) reachability to D0E(t) or L(t). New exact source-parent compositions exclude the high-stop target on two infinite root-index progressions, r≡9568 and r≡10592 (mod 16384); see Sections 7 and the linked detailed dossiers. The other root-index classes remain open. The integrated Lean theorem and complete U5B2Root32.lean import closure have not been compiled.

## 1. The same-parameter forward path

For every natural number \(u\), define

\[
\begin{aligned}
B_0(u)&=(734+10944u,\;34881+518816u),\\
S_1(u)&=(352256u+23690,\;348160u+23414),\\
S_2(u)&=(360448u+24243,\;344064u+23141),\\
S_3(u)&=(393216u+26450,\;327680u+22041),\\
Q(u)&=(524288u+35269,\;262144u+17635),\\
T(u)&=(1048576u+70538,\;3).
\end{aligned}
\]

The source-certified equivalence **BB6.Agent46.section_preimage_all_iff** gives the following five original-section edges. The displayed depth is the witness \(n\) in its predecessor grammar.

| Edge | Source branch | Depth | Sum identity | Companion cost identity |
|---|---|---:|---|---|
| \(B_0\to S_1\) | even \(a\) | 5 | \(700416u+47104=32(1472+21888u)\) | \(x+2y=1048576u+70518\) |
| \(S_1\to S_2\) | even \(a\) | 0 | \(704512u+47384=2(352256u+23692)\) | \(x+2y=1048576u+70525\) |
| \(S_2\to S_3\) | odd \(a\) | 0 | \(720896u+48492=2(360448u+24246)\), using \(x+y+1\) | \(x+2y=1048576u+70532\) |
| \(S_3\to Q\) | even \(a\) | 0 | \(786432u+52904=2(393216u+26452)\) | \(x+2y=1048576u+70539\) |
| \(Q\to T\) | odd \(a\), exceptional \(y=3\) | 0 | \(x+6=1048576u+70544=2a+6\) | \(x+10=1048576u+70548\) |

For the fifth edge, \(a=524288u+35269\), \(k=262144u+17635\), and \(2k=a+1\). The exceptional \(y=3\) branch of the complete predecessor grammar gives \(T(u)\).

The first four transitions also have the following exact FastSectionDef.exactSection durations, derived in the earlier branch calculation:

| Edge | Section duration |
|---|---:|
| \(B_0\to S_1\) | \(1037632u+69769\) |
| \(S_1\to S_2\) | \(696320u+46830\) |
| \(S_2\to S_3\) | \(688128u+46281\) |
| \(S_3\to Q\) | \(655360u+44084\) |

The source relation is the same one used by U5Y3ParentFan: SectionAllInverse.lean defines BB6.Agent46.secNext, and U5Y3ParentFan.lean imports it and opens that namespace. The five arithmetic witnesses are explicit, but the five-edge composition has not yet been wrapped in and compiled as one Lean theorem.

## 2. The residual parameter really is the B2 parameter

The standalone bridge theorem BB6.Agent3U5B2Root32ParameterBridge.u5_q0_root32_forces_h8_parameter assumes the original U5 residual equations

\[
211s+129=5\cdot2^{201+3360w},\qquad
32s=32+840w+m,
\]

the q=0 parent equation

\[
m+1=8(39+64h)+1,
\]

and \(w=6657+8192r\), \(E=201+3360w\), \(r\equiv32\pmod{64}\). It derives

\[
h=8+128u,\qquad
u=1802+6720t,\qquad
18018+211u+22155r=20\cdot2^{E-13}.
\]

Consequently,

\[
m+1=8(39+64(8+128u))+1=4409+65536u,
\]
so
\[
m=4408+65536u,\qquad T(u)=(16m+10,3).
\]

This resolves the earlier parameter-identification gap: the q=0 residual parent, the high-stop target, and the B2 path all use the same \(u\). The existing theorem blank_no_b2_root32_from_exact_root_index excludes \(B_0(u)\) under the exact root equation and root32 residue. It does **not** yet exclude \(T(u)\), because reachability cannot be transported backwards along a merely possible predecessor edge.

## 3. What reachability of the high-stop target forces

Suppose \(T(u)\) is reached and the U5 residual equations above hold. The original source predecessor theorem u5_residual_y3_parent_fan gives either the q=0 parent \(Q(u)\), or a branch with \(q\ge1\) and

\[
2^{2q-2}\mid m+1,\quad
a+3=2U,\quad
k+3q+1=U(2^{2q+1}-1).
\]

But \(m+1=4409+65536u\) is odd. Thus \(q\ge2\) is impossible, and the only possible nonzero branch is \(q=1\). Its parent is

\[
(2m-1,\;7m+3),
\]
whose coordinate sum is
\[
9m+2=39674+589824u\equiv2\pmod4.
\]
Its right coordinate is odd and at least five, so the existing all-time exclusion BB6.Agent11High.blank_no_odd_sum_two rules it out. Therefore

\[
T(u)\text{ reachable}\quad\Longrightarrow\quad Q(u)\text{ reachable}.
\]

This is the correct reverse-direction use of the U5 parent fan. It is stronger than observing the forward edge \(Q(u)\to T(u)\), but it still does not imply that \(B_0(u)\) was reached.

## 4. The unique inverse chain from Q to S1

For \(u=1802+6720t\), we have \(u\equiv2\pmod8\).

1. \(Q(u)\) is odd/odd, and
   \[
   Q_x+Q_y=786432u+52904\equiv8\pmod{16}.
   \]
   The existing oddodd_lowval_blank_reach_iff therefore transports reachability to its unique source parent \(S_3(u)\).

2. \(S_3(u)\) is even/odd, and
   \[
   S_{3,x}+S_{3,y}+1
   =720896u+48492
   =4(180224u+12123),
   \]
   where the final factor is odd. Hence its 2-adic valuation is exactly two. The complete section_preimage_all_iff grammar leaves only the odd-a, depth-zero parent \(S_2(u)\).

3. \(S_2(u)\) is odd/odd, with
   \[
   S_{2,x}+S_{2,y}=704512u+47384\equiv8\pmod{16}.
   \]
   A second application of oddodd_lowval_blank_reach_iff transports reachability to \(S_1(u)\).

Thus \(T(u)\) reachable forces \(S_1(u)\) reachable.

## 5. The S1 parent fan: two surviving families

For \(S_1\),

\[
S_{1,x}+S_{1,y}
=700416u+47104
=8(87552u+5888)
=8\cdot256(342u+23).
\]

Since \(u\) is even, \(342u+23\) is odd and greater than one. Hence the quotient has exact 2-adic valuation eight, and the total sum has valuation eleven.

The complete even_even_parent_fan gives:
- the direct parent
  \[
  D_0(u)=(700416u+47102,\;174080u+11706);
  \]
- the \(a=0\) branch, which would require \(87552u+5888\) to be a power of two and is impossible because it equals \(256(342u+23)\);
- an even-a bounce parent at odd depth \(n\). The valuation bound gives \(n\in\{1,3,5,7,9\}\).

The five bounce parents are:

| Depth | Parent |
|---:|---|
| 1 | \(P_1=(175104u+11774,\;436736u+29367)\) |
| 3 | \(P_3=(43776u+2942,\;502400u+33780)\) |
| 5 | \(B_0(u)=(734+10944u,\;34881+518816u)\) |
| 7 | \(P_7=(2736u+182,\;522920u+35154)\) |
| 9 | \(P_9=(684u+44,\;523946u+35220)\) |

Four depths are excluded:

- \(P_1\) has odd right coordinate and sum \(611840u+41141\equiv1\pmod4\), so blank_no_odd_sum_one excludes it.
- \(P_3\) has even right coordinate and sum \(546176u+36722\equiv2\pmod8\). blank_reach_iff_even_right forces its direct parent \((546176u+36720,\;251200u+16889)\), whose right coordinate is odd and whose sum is \(797376u+53609\equiv1\pmod4\). Hence \(P_3\) is excluded.
- \(B_0(u)\) is excluded by blank_no_b2_root32_from_exact_root_index.
- \(P_9\) has even right coordinate and sum \(524630u+35264\equiv4\pmod8\). Its forced direct parent is \((524630u+35262,\;261973u+17609)\), with odd right coordinate and sum \(786603u+52871\equiv1\pmod4\). Hence \(P_9\) is excluded.

The \(n=7\) parent \(P_7\) and the direct parent \(D_0\) remain. Therefore the current paper-level inverse reduction is

\[
T(u)\text{ reachable}\quad\Longrightarrow\quad
D_0(u)\text{ reachable}\ \lor\ P_7(u)\text{ reachable}.
\]

Both are even/even sum-zero targets with quotient congruent to three modulo four, so blank_no_sumzero_target applies if both of their own source parents can be excluded. Their exact two-parent fans are:

\[
\begin{aligned}
D_0(u)&:\quad
(874496u+58806,\;87040u+5852),\\
&\quad (218624u+14700,\;414976u+27902);
\\[2mm]
P_7(u)&:\quad
(525656u+35334,\;261460u+17576),\\
&\quad (131414u+8830,\;458581u+30824).
\end{aligned}
\]

The direct parent of \(D_0\) is already excluded: its sum is \(961536u+64658\equiv2\pmod8\), so its forced even-right predecessor is \((961536u+64656,\;43520u+2925)\), an odd-right target with sum \(1005056u+67581\equiv1\pmod4\). Thus reachability of \(D_0\) forces its bounce parent
\[
D_{0E}(u)=(218624u+14700,\;414976u+27902).
\]

The depth-seven parent \(P_7\) can be reduced further. Its bounce parent is
\[
P_{7E}(u)=(131414u+8830,\;458581u+30824).
\]
Write \(u=1802+6720t\). Two applications of the exact even-right reachability equivalence give

\[
\begin{aligned}
P_{7E,1}(t)&=(3964766400t+1063210642,\;1540832160t+413196892),\\
P_{7E,2}(t)&=(5505598560t+1476407532,\;770416080t+206598445).
\end{aligned}
\]

The first target has even right coordinate and sum \(3964766400t+1063210644\equiv4\pmod8\); the second has even right coordinate and sum \(5505598560t+1476407534\equiv6\pmod8\). Hence both even-right equivalences apply. But for the final target,
\[
x+y+1=6276014640t+1683005978\equiv2\pmod4.
\]
Its right coordinate is odd. The complete source grammar section_preimage_all_iff rules out every possible predecessor: the even-a branch needs \(x+y\) divisible by four, the odd-a branch needs \(x+y+1\) divisible by four, the low branch needs even \(y\), and the \(a=0,1\) exceptional branches need the corresponding stronger divisibility. Therefore \(P_{7E}(u)\) is unreachable.

The direct parent of \(P_7\) is
\[
P_{7D}(u)=(525656u+35334,\;261460u+17576).
\]
Its sum is \(787116u+52910\equiv6\pmod8\), so the even-right equivalence forces
\[
R_1(u)=(787116u+52908,\;130730u+8787).
\]
Here \(x+y+1=917846u+61696\) has exact 2-adic valuation two. Since \(x\) is even and \(y\) is odd, the complete source grammar leaves only the odd-a, depth-zero predecessor
\[
R_2(u)=\left(458923u+30845,\;\frac{589653u+39630}{2}\right).
\]
Substituting \(u=1802+6720t\),
\[
R_2(t)=(3083962560t+827010091,\;1981234080t+531297168).
\]
Its right coordinate is even and its coordinate sum is \(5065196640t+1358307259\equiv3\pmod8\), so another even-right equivalence forces
\[
L(t)=(5065196640t+1358307257,\;990617040t+265648583).
\]
This is odd/odd, with
\[
L_x+L_y=6055813680t+1623955840\equiv16t\pmod{32}.
\]
For odd \(t\), the existing oddodd_sum16_blank_reach_iff applies to \(L(t)\); for even \(t\), its sum is \(0\pmod{32}\), outside that theorem's current scope. Thus \(P_7\) reachability forces \(L(t)\) reachability, while the even-\(t\) high-valuation case remains open.

Combining the parent fans gives the sharper paper-level reduction
\[
T(u)\text{ reachable}\quad\Longrightarrow\quad
D_{0E}(t)\text{ reachable}\ \lor\ L(t)\text{ reachable}.
\]
This is not yet a Lean-compiled wrapper and does not prove \(T(u)\) unreachable. The two displayed affine families are the current residual source-orbit targets.

## 6. The exact root equation is saturated on the root32 cylinder

The root equation itself supplies no further modular exclusion within \(r\equiv32\pmod{64}\). In fact, for every \(j\ge0\), there is exactly one natural \(u\) satisfying it.

Put

\[
r=32+64j,\qquad
E=201+3360(6657+8192r),\qquad K=E-17.
\]

Then

\[
K=903171544+1761607680j
=184+3360(6657+8192r).
\]

Direct modular arithmetic gives

\[
2^{210}\equiv1\pmod{4431},\qquad
2^{184}\equiv3460\pmod{4431}.
\]

Since \(3360=16\cdot210\), it follows that \(2^K\equiv3460\pmod{4431}\). Therefore

\[
N=\frac{5\cdot2^K-17300}{22155}
\]
is an integer, because \(22155=5\cdot4431\).

Moreover \(K\ge22155j+3459\), so \(2^K\ge K+1\) gives \(N\ge j\). Set \(t=N-j\) and \(u=1802+6720t\). Substitution yields

\[
\begin{aligned}
18018+211u+22155r
&=64\bigl(17300+22155(t+j)\bigr)\\
&=64(17300+22155N)\\
&=320\cdot2^K\\
&=20\cdot2^{E-13}.
\end{aligned}
\]

For fixed \(r\), the equation is linear in \(u\) with nonzero coefficient 211, so this \(u\) is unique.

This is arithmetic feasibility only, not a blank-start execution. The root equation alone cannot eliminate any \(r=32+64j\) by further congruence filtering. The two exclusions below instead use original-source parent fans and blank-image invariants; the remaining work must likewise use the transition system.

## 7. Two composed high-stop exclusions

The exact root equation is saturated, but the source-orbit residuals are not. Two disjoint infinite root-index progressions are now excluded by closing **both** alternatives in the implication \(T(u)\) reachable \(\Rightarrow D_{0E}(t)\) reachable or \(L(t)\) reachable.

### 7.1. The progression r = 9568 (mod 16384)

For \(t\equiv47\pmod{256}\), the exceptional R parameter \(q=(t-3)/4\) is \(3\pmod8\), so the complete R parent fan excludes the D0E/E7 branch. On the L branch, the exact P0/A0/Q chain reaches the even/odd Q' family; at \(t=256n+47\), Q' has sum-plus-one \(4\pmod8\), hence a unique odd-a depth-zero parent. Its even-right inverse is an odd/odd state with sum \(2\pmod4\), excluded by blank_no_odd_sum_two. Thus both D0E and L are unreachable.

The root equation gives \(t+j\equiv196\pmod{256}\). Hence \(t\equiv47\) gives \(j\equiv149\) and \(r=32+64j\equiv9568\pmod{16384}\). The detailed source-parent composition is in [Root32HighStopR9568.md](Root32HighStopR9568.md).

### 7.2. The progression r = 10592 (mod 16384)

For \(t\equiv31\pmod{256}\), \(q=(t-3)/4\equiv7\pmod{64}\). The extended R parent fan excludes D0E/E7: its odd-a branch is forced to depth one and is excluded by blank_no_odd_sum_two; its direct branch passes through the even/even sum-zero fork, whose bounce parent is excluded by blank_no_odd_sum_one and whose direct parent is forced through a depth-zero odd-a parent and an even-right inverse to an odd/odd sum-two state. The L branch is forced through P0/A0/Q; Q has even right and sum \(6\pmod8\), so its unique parent is even/odd with sum \(1\pmod4\), excluded by blank_no_odd_sum_one.

Thus both alternatives are unreachable. The root equation gives \(j\equiv165\pmod{256}\), hence \(r\equiv10592\pmod{16384}\). The detailed composition is in [Root32HighStopR10592.md](Root32HighStopR10592.md).

The two progressions are nonempty and infinite by the exact-root saturation construction in Section 6. They are source-orbit exclusions, not mere congruence filters. All other root-index classes, and the global Machine C decision, remain open.

## 8. Verification boundary and next decisive action

- The five forward edges, the parameter identification, the q=0 parent reduction, and the S1 inverse-parent reduction are explicit algebraic derivations from the source-certified predecessor grammar and existing theorems.
- The standalone U5B2Root32ParameterBridge.lean has previously been compiled locally under Lean 4.36.0-rc2. The two new composed high-stop exclusions have **not** been wrapped and compiled in a single Lean module, and the full U5B2Root32.lean dependency closure remains uncompiled.
- No CI run is being treated as a substitute for the required local preflight.

The next decisive action is to compile and axiom-audit the exact compositions in Sections 7.1–7.2, then attack the remaining D0E/L parent families for other root indices. Do not spend effort on further root-equation-only congruence filtering.
