# First three terminal positions in the high-depth P1 restart suffix

**Agent 50 — 2026-11-21**

Status: conditional arithmetic reductions for the first three terminal positions of a genuine high-depth restart suffix. The third-position exclusion below is a new paper-level derivation; it has not been Lean-checked. This is intermediate work, not a P1 nonhalting proof or a BB(6) result.

## Claim

Assume a genuine source wall history has a last inverse edge of depth at least three, and consider the restart suffix after that edge. Use the notation and hypotheses of:

- `RestartWallSource.lean` and `RestartWallLowTrace.lean` in `im-results/agent9-p1-high-depth/`;
- `SIX-BIT-SLACK-MOD7.md` and `FirstShallowCoordinateGate.lean` in the same directory;
- `RestartDepthBounds.lean` for the high-depth defect identity.

The existing reductions leave exactly three first-shallow cases, denoted A, B, C below. In every case, the first-shallow child is not the wall endpoint. The result here is that the child of the *next* low-depth edge is also not the wall endpoint.

Consequently, after the first shallow edge, a wall-reaching restart suffix must contain at least two further inverse transitions. This does **not** say that either further transition is shallow.

## Common notation and source equations

Put \(P=2^n\), \(M=m_0+n\), and \(D=d_0-1=c_0+3\), where \((b_0,d_0,m_0)\) is the restart child immediately after the last depth-\(\ge3\) edge and \(c_0\) is that edge's odd inverse parameter. Thus \(D\ge4\).

The source restart identity is
\[
49D+14M-6=(98-2^\delta I_s)P.
\]
The three residual branches have \((\delta,I_s)=(2,20)\) in A and \((1,48)\) in B,C. In particular, in B and C,
\[
49D+14M=2P+6. \tag{1}
\]

The wall cost congruence implies \(n\) is even: in
\[
\sum_{s\in B}(n+3+s)2^s\equiv1\pmod{2^n},
\]
the set \(B\) contains \(0\), while all terms with \(s>0\) are even, so \(n+3\) is odd. The slack cases give \(n\equiv1\pmod3\) in A and \(n\equiv2\pmod3\) in B,C.

Let \(T=M+6+3s\) be the offset at the first-shallow parent. The existing first-shallow reduction gives:

| Case | \(I_s\) | \(T\) | first shallow depth \(t_1\) | \(M\) |
|---|---:|---:|---:|---:|
| A | 20 | \(14u+5\) | 0 | \(14u-n-3\) |
| B | 48 | \(14u+10\) | 0 | \(14u-n+3\) |
| C | 48 | \(14u+3\) | 1 | \(14u-n-4\) |

The first-shallow child coordinates, obtained from the source inverse power and mass equations, are:

| Case | \(b_1\) | \(d_1\) |
|---|---|---|
| A | \(6P-12u-12\) | \(8P-16u-1\) |
| B | \(6P-12u-16\) | \(8P-16u-7\) |
| C | \(10P-20u-12\) | \(4P-8u+1\) |

The already-proved first-child terminal exclusions in `FirstShallowCoordinateGate.lean` show that this child is not the wall endpoint. Hence a next edge exists. Since this is the suffix after the last depth-\(\ge3\) edge, its depth \(r\) is one of \(0,1,2\).

## Eliminate a wall endpoint after that next edge

Suppose, for contradiction, that the child of this second edge is the wall endpoint. Let its inverse parameter be \(c_2\), and let \(B_2=T+t_1+r+2\) be the offset after the two transitions. The exact source equations are
\[
2^r(c_2+3)=d_1+b_1/2+3,
\]
\[
2k_2+c_2+2r+2=b_1+d_1,\qquad b_2=2k_2-4,
\]
and the wall equation is
\[
b_2+4B_2=12P+4.
\]
Eliminating \(k_2,b_2,c_2\) gives
\[
d_1+b_1/2+3
=2^r\bigl(b_1+d_1+4T+4t_1+2r+1-12P\bigr). \tag{2}
\]

Substituting the three coordinate rows into (2) yields the following necessary equations:

| Case | \(r=0\) | \(r=1\) | \(r=2\) |
|---|---|---|---|
| A | \(9P=50u+12\) | \(7P=78u+24\) | \(3P=134u+52\) |
| B | \(9P=50u+30\) | \(7P=78u+52\) | \(3P=134u+100\) |
| C | \(7P=46u+8\) | \(5P=74u+18\) | \(P=130u+42\) |

Every entry is impossible:

### Case A

- \(r=0\): modulo \(25\), \(P\equiv18\). But for even \(n\), \(2^n\bmod25\) lies in \(\{1,4,16,14,6,24,21,9,11,19\}\), excluding \(18\).
- \(r=1\): modulo \(3\), \(P\equiv0\), impossible for \(P=2^n\).
- \(r=2\): modulo \(67\), \(P\equiv62=2^{48}\). The order of \(2\) modulo \(67\) is \(66\), so \(n\equiv48\pmod{66}\), contradicting \(n\equiv1\pmod3\).

### Case B

- \(r=0\): modulo \(25\), \(P\equiv20\), again impossible for even \(n\).
- \(r=1\): the equation gives
  \[
  u=(7P-52)/78,\qquad
  M=14u-n+3=(49P-39n-247)/39.
  \]
  Hence
  \[
  M-P/7=(304P-273n-1729)/273>0
  \]
  for \(n\ge83\), since \(P=2^n\ge2n\). But (1) and \(D\ge4\) imply
  \[
  14M\le2P+6-196=2P-190,
  \]
  so \(M<P/7\), a contradiction.
- \(r=2\): modulo \(67\), \(P\equiv11=2^{59}\). Since the order is \(66\), \(n\equiv59\pmod{66}\), contradicting that \(n\) is even.

### Case C

- \(r=0\): modulo \(23\), \(P\equiv11\). The powers of \(2\) modulo \(23\) are \(\{1,2,4,8,16,9,18,13,3,6,12\}\), so \(11\) is not a power of \(2\).
- \(r=1\): modulo \(37\), \(P\equiv11=2^{30}\). The order of \(2\) modulo \(37\) is \(36\), so \(n\equiv30\pmod{36}\), contradicting \(n\equiv2\pmod3\).
- \(r=2\): modulo \(13\), \(P\equiv3=2^4\). The order of \(2\) modulo \(13\) is \(12\), so \(n\equiv4\pmod{12}\), again contradicting \(n\equiv2\pmod3\).

Thus the second low-depth edge cannot terminate at the wall in any of the three surviving first-shallow branches.

## Composition with the source-authentic restart path

The source-level composition is as follows.

1. `source_wall_restart_suffix_shape` in `RestartWallSource.lean`, under (n\ge14), a root `OddCone` history, the exact wall equation, and `HasDeep`, supplies a genuine `RestartPath` after the last depth-(ge3) edge. It also gives the suffix shape: there is a shallow edge, and every inverse edge after the last shallow edge has depth exactly two.
2. `restartPath_first_shallow_state` in `RestartWallLowTrace.lean` extracts the first shallow edge from that same source path. Its preceding source `OddCone` prefix has only depth-two edges, and it retains the actual `inverseAt` parent/child and restart-walk split. This is the source-authentic input to the three-branch reduction.
3. For (n\ge83), the `SIX-BIT-SLACK-MOD7.md` / `FirstShallowCoordinateGate.lean` reduction leaves A, B, C above. Its existing `is20_terminal_impossible_pow`, `is48_even_terminal_impossible_pow`, and `is48_odd_terminal_impossible_pow` lemmas exclude a wall at the first-shallow child. The calculation in this note excludes a wall at the child of the immediately following low edge; the new section below excludes the wall at the child of the third edge.

Thus, conditional on the cited source theorems and the three-branch reduction, neither the first-shallow edge, nor the next edge, nor the third edge can be the final edge of the restart suffix. The source path must continue through a fourth edge after the first-shallow parent. The second, third, and later transitions may still have depth two; the last-shallow suffix theorem says that once the last shallow edge is reached, every remaining edge has depth exactly two.

**Answer to the composition question:** the first-shallow child and the child after the next edge cannot be the wall endpoint. The third-edge calculation below also excludes the child after the following edge. A wall-reaching restart suffix must therefore contain at least four transitions beginning at the first-shallow parent (the first shallow edge plus three subsequent low-depth edges). This is a finite prefix-length lower bound only; it does not bound later shallow edges or establish an all-time exclusion.

This composition is a paper-level dependency argument only. The exact Lean dependency closure and exported theorem axioms were not compiled/audited in this invocation because the local shell/runtime returned a CAAS ClientError. The result remains intermediate until that source-level composition is formalized and checked.


## Exclude a wall endpoint after the third edge

Let \((b_1,d_1)\) be the child immediately after the first shallow edge, and set
\[
X_1=d_1+b_1/2+3,\qquad S_1=b_1+d_1.
\]
The three surviving first-shallow branches give the following exact coordinates. Here \(T\) is the offset at the first-shallow parent, and \(t_1\) is that edge's depth.

| Branch | \(t_1\) | \(T\) | \(X_1\) | \(S_1\) | \(M\) | Restart defect |
|---|---:|---:|---:|---:|---:|---|
| A (\(I_s=20\)) | 0 | \(14u+5\) | \(11P-22u-4\) | \(14P-28u-13\) | \(14u-n-3\) | \(49D+14M=18P+6\) |
| B (\(I_s=48\), even \(T\)) | 0 | \(14u+10\) | \(11P-22u-12\) | \(14P-28u-23\) | \(14u-n+3\) | \(49D+14M=2P+6\) |
| C (\(I_s=48\), odd \(T\)) | 1 | \(14u+3\) | \(9P-18u-2\) | \(14P-28u-11\) | \(14u-n-4\) | \(49D+14M=2P+6\) |

Assume that the child after the third edge is the wall endpoint. Let \(r\in\{0,1,2\}\) be the depth of the second edge and \(v\in\{0,1,2\}\) the depth of the third edge. For the second edge, the exact source equations are
\[
2^r(c_2+3)=X_1,\qquad 2k_2+c_2+2r+2=S_1,
\]
and its child is \((b_2,d_2)=(2k_2-4,c_2+4)\). Consequently
\[
X_2=d_2+b_2/2+3
   =\frac{S_1+X_1/2^r+5-2r}{2},\qquad
S_2=b_2+d_2=S_1-2r-2.
\]
The offset after the third edge is \(B_3=T+t_1+r+v+3\). Applying the same source power and mass equations to the third edge and imposing the wall equation gives
\[
X_2=2^v(S_2+4B_3-12P-2v-7).
\]
After substitution and multiplication by \(2^{r+1}\), this is a linear equation \(aP=bu+c\). The complete \(3\times3\) case table is:

| Branch | \(r=0\), \(v=0,1,2\) | \(r=1\), \(v=0,1,2\) | \(r=2\), \(v=0,1,2\) |
|---|---|---|---|
| A | \(21P=106u+32\); \(17P=162u+60\); \(9P=274u+124\) | \(31P=190u+72\); \(23P=302u+136\); \(7P=526u+280\) | \(51P=358u+164\); \(35P=582u+308\); \(3P=1030u+628\) |
| B | \(21P=106u+70\); \(17P=162u+118\); \(9P=274u+222\) | \(31P=190u+140\); \(23P=302u+244\); \(7P=526u+468\) | \(51P=358u+292\); \(35P=582u+516\); \(3P=1030u+996\) |
| C | \(19P=102u+24\); \(15P=158u+48\); \(7P=270u+104\) | \(29P=186u+58\); \(21P=298u+114\); \(5P=522u+242\) | \(49P=354u+138\); \(33P=578u+266\); \(P=1026u+554\) |

For \(n\ge83\), \(P=2^n\ge100n\). The equations are all impossible:

### Branch A

For \((r,v)=(0,0),(0,1),(1,0),(2,0)\), cross-multiplication in the displayed equations gives \(u>P/10\). Since \(M=14u-n-3\),
\[
M>\frac{7P}{5}-n-3>\frac{9P}{7},
\]
where the last inequality follows from \(P\ge100n\) and \(n\ge83\). But \(D\ge4\) and \(49D+14M=18P+6\) imply \(M\le(18P-190)/14<9P/7\), a contradiction.

The other five pairs are excluded by exact modular obstructions:
- \((0,2)\): \(9P=274u+124\) gives \(P\equiv29\pmod{137}\). Since \(137\equiv1\pmod8\), \(2\) is a quadratic residue, whereas \(29^{68}\equiv-1\pmod{137}\).
- \((1,1)\): \(23P=302u+136\) gives \(P\equiv65\pmod{151}\); \(2\) is a quadratic residue modulo \(151\), whereas \(65^{75}\equiv-1\pmod{151}\).
- \((1,2)\): \(7P=526u+280\) gives \(P\equiv40\pmod{263}\); \(2\) is a quadratic residue modulo \(263\), whereas \(40^{131}\equiv-1\pmod{263}\).
- \((2,1)\): \(35P=582u+308\) gives \(P\equiv67\pmod{97}\); \(2\) is a quadratic residue modulo \(97\), whereas \(67^{48}\equiv-1\pmod{97}\).
- \((2,2)\): \(3P=1030u+628\) gives \(P\equiv72\pmod{103}\). In branch A, \(n\equiv4\pmod6\), so \(P=16\cdot64^q\) for some \(q\). But \(64^{17}\equiv1\pmod{103}\), while \(72\cdot16^{-1}\equiv56\pmod{103}\) and \(56^{17}\equiv46\pmod{103}\).

### Branch B

For every pair except \((r,v)=(2,2)\), the equation gives \(u>P/90\). Then
\[
M=14u-n+3>\frac{7P}{45}-n+3>\frac P7,
\]
using \(P\ge100n\), contradicting \(49D+14M=2P+6\) and \(D\ge4\), which imply \(M\le P/7-95/7\).

For \((2,2)\), \(3P=1030u+996\) gives \(P\equiv2\pmod5\), impossible because \(n\) is even and hence \(2^n\equiv1\) or \(4\pmod5\).

### Branch C

For every pair except \((r,v)=(1,2),(2,2)\), the equation gives \(u>P/90\). Hence
\[
M=14u-n-4>\frac{7P}{45}-n-4>\frac P7,
\]
again contradicting the defect bound.

For \((1,2)\), \(5P=522u+242\) gives \(P\equiv2\pmod{29}\). Since \(2^{14}\equiv-1\pmod{29}\), the order of \(2\) modulo \(29\) is \(28\); thus \(2^n\equiv2\pmod{29}\) would force \(n\) odd, contrary to the even-\(n\) wall condition. For \((2,2)\), \(P=1026u+554\) gives \(P\equiv2\pmod3\), whereas \(n\) even gives \(2^n\equiv1\pmod3\).

Therefore the wall endpoint cannot occur after the third edge in any of the three first-shallow branches.

**Scope.** This is an exact paper-level arithmetic exclusion conditional on the cited restart and first-shallow reductions. It extends the terminal-position analysis by one edge: the source suffix must contain at least four edges from the first-shallow parent. The derivation is not yet a Lean theorem or an original-source accepted composition. It does not exclude a fourth-or-later terminal edge, bound the remaining shallow-edge pattern, or decide P1/BB(6).

## Research consequence and limits

The combined first-, second-, and third-edge exclusions show that a genuine restart suffix cannot reach the wall at any of those first three positions after the first-shallow parent; it must contain at least a fourth edge.

The next unresolved case is a fourth or later low-depth transition. In particular, the argument does not exclude a suffix in which the third edge is followed by a longer depth-two tail, nor does it bound the number of later shallow edges. It is therefore not the unrestricted six-shallow lemma, a P1 nonhalting proof, or a BB(6) upper bound.

The derivation is source-conditional through the cited restart and first-shallow theorems. The modular case checks above are elementary; the complete statement should be formalized in Lean and composed with `source_wall_restart_suffix_shape` before being promoted beyond `im-results/`.
