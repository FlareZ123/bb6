# Second-edge terminal exclusion in the high-depth P1 restart

**Agent 50 — 2026-11-21**

Status: exact conditional arithmetic lemma derived from the source restart and first-shallow reductions. This is an intermediate result, not a P1 nonhalting proof and not a BB(6) result. It has not been Lean-checked in this invocation because the local shell/container is unavailable.

## Claim

Assume a genuine source wall history has a last inverse edge of depth at least three, and consider the restart suffix after that edge. Use the notation and hypotheses of:

- \`RestartWallSource.lean\` and \`RestartWallLowTrace.lean\` in \`im-results/agent9-p1-high-depth/\`;
- \`SIX-BIT-SLACK-MOD7.md\` and \`FirstShallowCoordinateGate.lean\` in the same directory;
- \`RestartDepthBounds.lean\` for the high-depth defect identity.

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

The already-proved first-child terminal exclusions in \`FirstShallowCoordinateGate.lean\` show that this child is not the wall endpoint. Hence a next edge exists. Since this is the suffix after the last depth-\(\ge3\) edge, its depth \(r\) is one of \(0,1,2\).

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
| B | \(9P=50u+30\) | \(7P=78u+28\) | \(3P=134u+68\) |
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
  u=(7P-28)/78,\qquad
  M=14u-n+3=(49P-39n-79)/39.
  \]
  Hence
  \[
  M-P/7=(304P-273n-553)/273>0
  \]
  for \(n\ge83\), since \(P=2^n\ge2n\). But (1) and \(D\ge4\) imply
  \[
  14M\le2P+6-196=2P-190,
  \]
  so \(M<P/7\), a contradiction.
- \(r=2\): modulo \(67\), \(P\equiv45=2^{27}\). Since the order is \(66\), \(n\equiv27\pmod{66}\), contradicting that \(n\) is even.

### Case C

- \(r=0\): modulo \(23\), \(P\equiv11\). The powers of \(2\) modulo \(23\) are \(\{1,2,4,8,16,9,18,13,3,6,12\}\), so \(11\) is not a power of \(2\).
- \(r=1\): modulo \(37\), \(P\equiv11=2^{30}\). The order of \(2\) modulo \(37\) is \(36\), so \(n\equiv30\pmod{36}\), contradicting \(n\equiv2\pmod3\).
- \(r=2\): modulo \(13\), \(P\equiv3=2^4\). The order of \(2\) modulo \(13\) is \(12\), so \(n\equiv4\pmod{12}\), again contradicting \(n\equiv2\pmod3\).

Thus the second low-depth edge cannot terminate at the wall in any of the three surviving first-shallow branches.

## Research consequence and limits

This closes the next terminal case in the high-depth restart analysis: a genuine restart suffix cannot reach the wall at the first-shallow child or at the child of the immediately following low-depth edge.

The next unresolved case is a third or later low-depth transition. In particular, the argument does not exclude a suffix in which the second edge has depth two and is followed by a longer depth-two tail, nor does it bound the number of later shallow edges. It is therefore not the unrestricted six-shallow lemma, a P1 nonhalting proof, or a BB(6) upper bound.

The derivation is source-conditional through the cited restart and first-shallow theorems. The modular case checks above are elementary; the complete statement should be formalized in Lean and composed with \`source_wall_restart_suffix_shape\` before being promoted beyond \`im-results/\`.
