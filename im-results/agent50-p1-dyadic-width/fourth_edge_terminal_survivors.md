# Fourth-edge terminal survivors in the P1 restart wall

**Agent 50 — 23 November 2026**

**Status.** Exact integer classification of all 81 fourth-edge depth triples. Seventy-nine are excluded by the existing first-shallow defect bounds or a complete modular-period test. Two A-branch cases survive, and each extends to an infinite arithmetic family of locally source-valid restart suffixes, including a preceding depth-five or depth-seven edge. These are **not blank-root histories** and do not decide P1 or BB(6). This is intermediate research and belongs in the investigation area, not the academic results index.

## 1. Terminal equation after four shallow-or-low edges

Put \(P=2^n\). Use the first-shallow branch coordinates from [the three-edge analysis](restart_second_edge_terminal_exclusion.md). For branches A, B, C respectively, the state immediately after the first shallow edge has coordinates \((S_1,X_1,T,t_1)\):

| Branch | \(t_1\) | \(T\) | \(S_1\) | \(X_1\) | \(n\bmod 6\) |
|---|---:|---|---|---|---:|
| A | 0 | \(14u+5\) | \(14P-28u-13\) | \(11P-22u-4\) | 4 |
| B | 0 | \(14u+10\) | \(14P-28u-23\) | \(11P-22u-12\) | 2 |
| C | 1 | \(14u+3\) | \(14P-28u-11\) | \(9P-18u-2\) | 2 |

Here \(T=m+n+6\) is the offset coordinate, and \(S=b+d,\ X=d+b/2+3\). The first-shallow parent is one edge before this state.

Let \(r,v,w\in\{0,1,2\}\) be the depths of the next three edges. For an edge of depth \(t\), the exact source recurrence is

\[
S'=S-2t-2,\qquad
X'=\frac{S+X/2^t+5-2t}{2}.
\]

Consequently,

\[
S_2=S_1-2r-2,\quad
X_2=\frac{S_1+X_1/2^r+5-2r}{2},
\]

\[
S_3=S_1-2r-2v-4,\quad
X_3=\frac{S_2+X_2/2^v+5-2v}{2}.
\]

The terminal wall condition for the fourth edge is

\[
X_3=2^w\bigl(S_3+4(T+t_1+r+v+w+4)-12P-2w-7\bigr).
\]

After simplification, the exact integer equation is

\[
\begin{aligned}
&2^{r+v+1}(S_1+3-2r-2v)
 +2^r(S_1+5-2r)+X_1\\
&\qquad=2^{r+v+w+2}
 (S_1+4T+4t_1+2r+2v+2w+5-12P).
\end{aligned}
\tag{4E}
\]

Substituting each branch's affine coordinates and dividing the common gcd gives one equation

\[
aP=bu+c
\]

for each of the 81 branch/depth triples. The accompanying executable [exact scan](fourth_edge_terminal_scan.js) regenerates all coefficients and the classification below using exact BigInt arithmetic only.

## 2. Exhaustive 81-case classification

The branch-specific defect equations from the first-shallow reduction are

\[
49D+14M=
\begin{cases}
18P+6 & \text{A},\\
2P+6 & \text{B or C},
\end{cases}
\qquad D\ge4.
\]

With the branch definitions of \(M\), they imply

\[
u\le
\begin{cases}
9P/98+n/14-37/49 & \text{A},\\
P/98+n/14-58/49 & \text{B},\\
P/98+n/14-67/98 & \text{C}.
\end{cases}
\tag{DB}
\]

For A define \(\delta=98a-9b\); for B and C define \(\delta=98a-b\). Across the 81 equations:

- every \(a,b,c\) is positive;
- \(b\le8198\), \(c\le9700\);
- among the 56 rows with \(\delta>0\), the minimum \(\delta\) is 160.

For each such row, multiplying the difference between \(u=(aP-c)/b\) and its bound (DB) by \(98b\) gives at least

\[
160P-7(8198)n-98(9700)>0.
\]

The last inequality holds for \(n\ge83\), since \(2^n\ge100000n\) there. Thus all 56 positive-slope rows contradict the defect bound.

For each of the remaining 25 rows, reduce \(aP=bu+c\) modulo \(b\). Divide by \(g=\gcd(a,b)\), reject if \(g\nmid c\), then remove the full power of two from \(b/g\). Since \(n\ge83\), the power-of-two part is forced to zero; the odd part requires one residue of \(2^n\). The scan tests a full period jointly with the branch's fixed \(n\bmod6\): the order of 2 modulo the odd modulus is at most its Euler totient, hence at most the modulus minus one. This is a complete modular-period test, not a bounded sample of exponents.

It excludes 23 more rows. Exactly two survive:

| Branch | \((r,v,w)\) | Reduced terminal equation | Odd modulus condition |
|---|---|---|---|
| A | \((0,1,2)\) | \(17P=1058u+636\) | \(2^n\equiv193\pmod{529}\) |
| A | \((1,1,1)\) | \(87P=1198u+712\) | \(2^n\equiv139\pmod{599}\) |

The counts are therefore **56 defect exclusions + 23 modular exclusions + 2 survivors = 81**.

## 3. Both survivors extend to locally source-valid restart suffixes

For both cases, branch A gives

\[
M=14u-n-3,\qquad
D=\frac{18P+14n+48-196u}{49}.
\tag{D}
\]

Because \(196\) is divisible by 49, integrality of \(D\) is equivalent to

\[
18\cdot2^n+14n+48\equiv0\pmod{49}.
\tag{49}
\]

Also \(D\) is even. Let \(s=(n+2)/3\), which is an integer because branch A has \(n\equiv4\pmod6\).

The following two infinite subfamilies additionally satisfy \(n\equiv2\pmod{16}\), so they meet the existing low-order wall residue filter:

### Case I: depths \((r,v,w)=(0,1,2)\)

\[
n\equiv5362\pmod{595056},\qquad
u=\frac{17P-636}{1058}.
\]

The period is \(\operatorname{lcm}(48,147,253)=595056\), where \(\operatorname{ord}_{529}(2)=253\) and the condition (49) has period 147. At the base index \(n=5362\),

\[
2^n\equiv193\pmod{529},\qquad
18\cdot2^n+14n+48\equiv0\pmod{49}.
\]

For every index in this progression, \(u\) is an integer and

\[
u\equiv34\pmod{64}.
\]

The low-edge states after the first shallow edge are

\[
S_1=14P-28u-13,\quad X_1=11P-22u-4,
\]

\[
S_2=14P-28u-15,\quad
X_2=(25P-50u-12)/2,
\]

\[
S_3=14P-28u-19,\quad
X_3=(81P-162u-60)/8.
\]

The final depth-two wall equation is \(X_3=8P+112u+72\), exactly equivalent to \(17P=1058u+636\). The three source transitions of depths \(0,1,2\) satisfy the power, odd-\(c\), even-\(k\), and child-state guards because \(u\equiv34\pmod{64}\).

### Case II: depths \((r,v,w)=(1,1,1)\)

\[
n\equiv9538\pmod{703248},\qquad
u=\frac{87P-712}{1198}.
\]

Here \(\operatorname{lcm}(48,147,299)=703248\), with \(\operatorname{ord}_{599}(2)=299\). At \(n=9538\),

\[
2^n\equiv139\pmod{599},\qquad
18\cdot2^n+14n+48\equiv0\pmod{49}.
\]

For every index in this progression, \(u\) is an integer and

\[
u\equiv4\pmod{64}.
\]

The low-edge states are

\[
S_2=14P-28u-17,\quad
X_2=(39P-78u-24)/4,
\]

\[
S_3=14P-28u-21,\quad
X_3=(151P-302u-136)/16.
\]

The final depth-one wall equation is \(X_3=4P+56u+36\), exactly equivalent to \(87P=1198u+712\). The three source transitions of depths \(1,1,1\) satisfy the same source guards because \(u\equiv4\pmod{64}\).

## 4. The depth-two prefix and a genuine deep predecessor

The first-shallow parent state in branch A is

\[
b_s=12P-24u-12,\qquad d_s=2P-4u+1,\qquad T=14u+5.
\]

For a depth-two edge, reversing the source power/mass equations from child \((b',d')\) to parent \((b,d)\) gives

\[
b=2b'-6d'+26,\qquad d=7d'-b'-20.
\]

In coordinates \(\rho=b-6d\) and \(\sigma=b+d\), this is simply

\[
\rho'=8\rho+146,\qquad \sigma'=\sigma+6.
\]

At the first-shallow parent, \(\rho=-18\) and \(\sigma=14P-28u-11\). Reversing \(s=(n+2)/3\) depth-two edges yields

\[
\rho_s=\frac{80P-146}{7},\qquad
\sigma_s=14P-28u+2n-7.
\]

The resulting restart state has

\[
d_R=\frac{\sigma_s-\rho_s}{7}=D+1,\qquad
b_R=\sigma_s-d_R,\qquad
m_R=14u-2n-3.
\]

All intermediate reverse states are legal: \(b_s\equiv0\pmod4\) and \(d_s\) is odd, properties preserved by the reverse map; \(b_j\) increases when reversing; and \(d_j=(\sigma_j-\rho_j)/7\) is positive throughout because \(\sigma_j-\rho_j\) is concave in \(j\) and positive at both endpoints. The mass invariant \(b+d+2(m+n+6)+1=14P\) is preserved exactly.

There is also a valid predecessor edge of depth at least three into this restart state. Set \(V=b_R+d_R\). For a chosen depth \(t\), the parent of the restart state is

\[
d_p=2^{t+1}D-V-2t-8,\qquad
b_p=2V+4t+10-2^{t+1}D,\qquad
m_p=m_R-t-1.
\]

- In Case I, choose \(t=5\). The formulas simplify to
  \[
  d_p=(466P-11172u+798n+2533)/49,
  \]
  \[
  b_p=(220P+9800u-700n-2288)/49.
  \]
- In Case II, choose \(t=7\). They simplify to
  \[
  d_p=(3922P-48804u+3486n+11553)/49,
  \]
  \[
  b_p=(-3236P+47432u-3388n-11112)/49.
  \]

Substitution gives explicit positivity certificates. In Case I,

\[
1058\cdot49\,d_p
=303104P+11172\cdot636+1058(798n+2533)>0,
\]
\[
1058\cdot49\,b_p
=399360P-740600n-8653504>0.
\]

In Case II,

\[
1198\cdot49\,d_p
=452608P+48804\cdot712+1198(3486n+11553)>0,
\]
\[
1198\cdot49\,b_p
=249856P-4058824n-47083760>0.
\]

The two negative-tail inequalities follow immediately from \(P=2^n\ge100000n\) for \(n\ge83\); in particular \(b_p>8\) and \(d_p\ge1\). Also \(u>aP/(2b)\) in each family, so \(m_p=14u-2n-t-4>n\) (with \((a,b,t)=(17,1058,5)\) or \((87,1198,7)\)). Since \(b_R\equiv0\pmod4\), \(d_R\) is odd, \(D=d_R-1\) is even, and \(V=b_R+d_R\) is odd, the formulas give \(b_p\equiv0\pmod4\) and \(d_p\) odd. Finally \(c=d_R-4\) is odd and \(k=(b_R+4)/2\) is even and at least two. Thus the preceding depth-five/depth-seven transition satisfies the exact source power/mass and parity conditions.

The resulting local depth words, in forward order from the synthetic parent to the wall, are

\[
[5],\ [2]^s,\ [0,0,1,2]
\quad\text{and}\quad
[7],\ [2]^s,\ [0,1,1,1].
\]

The executable scan verifies the complete local source guards and terminal equality at the first indices \(n=5362\) and \(n=9538\), including all \(s\) depth-two steps.

## 5. What this does and does not establish

This is a real obstruction to extending the previous three-edge argument by merely enumerating the next local terminal edge. The two surviving families are not artifacts of a relaxed parity calculation: they have exact locally source-valid suffixes with a preceding high-depth edge.

They are **not** blank-root witnesses. Their synthetic parent costs are

\[
m_p=14u-2n-t-4>n
\]

for \(n\ge83\). The complete source-wall congruence

\[
\sum_{s\in A_n}(n+3+s)2^s\equiv1\pmod{2^n}
\]

therefore still has to be supplied entirely by the missing prefix before this parent: all suffix start costs are at least \(m_p>n\) and vanish modulo \(2^n\). The exact modular subset scan in [Agent 43's finite all-depth carry result](../agent43-p1-high-cost-reset-count/WallFullDPTo10000.md) finds only six possible indices for \(14\le n\le10000\); neither 5362 nor 9538 is among them. This is finite computational evidence, not an all-time proof.

**Research direction:** stop extending local terminal-position case tables as though they could decide the blank-root problem. The decisive missing result is an all-time restriction on the root prefix's cumulative-cost subset (or a source-connected construction of such a prefix) for the arithmetic progressions above. The density-zero shallow-gap theorem in [six_shallow_sparse_candidates.md](six_shallow_sparse_candidates.md) is not enough: it leaves a zero-density exceptional set.

No Lean claim is made for this note. The local compiler was unavailable in this invocation, and the repository's Critic instruction explicitly forbids substituting a full manual CI run for the required local leaf preflight.