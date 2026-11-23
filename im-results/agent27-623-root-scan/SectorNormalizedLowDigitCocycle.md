# Scaled \((p,q)\) cocycle and drain residues for #623

**Status:** exact algebraic reduction of the source-derived canonical-ray \((p,q)\) recurrence, with a finite-state mod-3 lift of its drain statistics. This is not an all-time root invariant, a halting/nonhalting proof, or a BB(6) result.

**Important scope correction:** this is a \((p,q)\)-coordinate result only. Do not identify the scaled coordinate \(P=2p\) below with Agent 1's signed-window coordinate \(V=X+Y\), and do not use the \((p,q)\) corrections \(\beta,\delta\) as replacements for the Lean-checked signed-window corrections \(\mathrm{corrC},\mathrm{corrF}\). Agent 1's corrected synchronization cocycle is a separate exact system.

## 1. Canonical \((p,q)\) recurrence

For a canonical state \(D(a,d)\), put
\[
p=|a-d|,\qquad q=\min(a,d).
\]
In each input sector, the unsorted next counters are
\[
A=p+\beta_s,\qquad E=3q+\delta_s.
\]
Write \(T_s=\delta_s-\beta_s\). Sorting \(A,E\) gives
\[
p'=|p-3q-T_s|,\qquad q'=\min(p+\beta_s,\,3q+\delta_s).
\]
The output is left-oriented when \(p-3q\ge T_s\), and right-oriented otherwise:
\[
\begin{array}{c|cc}
& p'&q'\\ \hline
L&p-3q-T_s&3q+\delta_s\\
R&3q+T_s-p&p+\beta_s.
\end{array}
\]

The exact correction table in the canonical-ray convention is:

| Sector | \(\beta_s\) | \(\delta_s\) | \(T_s=\delta_s-\beta_s\) |
|---|---:|---:|---:|
| LO | \(-D-5\) | \(2D+2r+14\) | \(3D+2r+19\) |
| LE | \(-D-2\) | \(2D+2r+8\) | \(3D+2r+10\) |
| RO | \(4-D\) | \(2D+2r\) | \(3D+2r-4\) |
| RE | \(1-D\) | \(2D+2r+5\) | \(3D+2r+4\) |

Here \(D\) is the signed drop. In RE, the initial evaluator's signed drop is included in \(D\), while \(r\) counts subsequent drain iterations. If \(R_{\rm full}\) is the full evaluator-call count, then \(r=R_{\rm full}-1\) in RE and \(r=R_{\rm full}\) in the other sectors.

## 2. Scaled integer coordinates

Define
\[
\boxed{Q=6q,\qquad P=2p.}
\]
These are merely scaled canonical counters; they are not Agent 1's synchronization coordinates \(U,V\).

The exact integer updates become:

**Left output**
\[
\boxed{Q'=3Q+6\delta_s,\qquad P'=P-Q-2T_s.}
\]

**Right output**
\[
\boxed{Q'=3P+6\beta_s,\qquad P'=Q-P+2T_s.}
\]

These follow directly by multiplying the two \((p,q)\) branch equations by 6 and 2, respectively.

## 3. Exact mod-3 quotient and sector normalization

Since \(Q=6q\equiv0\pmod3\), the active quotient \(Q'/3\) and passive residue \(P'\) satisfy
\[
\begin{array}{c|cc}
&L&R\\ \hline
Q'/3&D+r+2c_\delta(s)&P+D+2c_\beta(s)\\
P'&P-r-2c_T(s)&-P+r+2c_T(s)
\end{array}\pmod3,
\]
where
\[
c_\beta=(-5,-2,4,1),\quad
c_\delta=(14,8,0,5),\quad
c_T=(19,10,-4,4)
\]
in LO, LE, RO, RE order.

Because \(2c_\beta(s)\equiv2\pmod3\) in every sector, this is
\[
\begin{array}{c|cc}
s&L:(Q'/3,P')&R:(Q'/3,P')\\ \hline
LO&(D+r+1,\ P-r+1)&(P+D+2,\ -P+r+2)\\
LE&(D+r+1,\ P-r+1)&(P+D+2,\ -P+r+2)\\
RO&(D+r,\ P-r+2)&(P+D+2,\ -P+r+1)\\
RE&(D+r+1,\ P-r+1)&(P+D+2,\ -P+r+2)
\end{array}\pmod3.
\]

A sector translation makes the passive rule simpler. Put
\[
\widehat P=P+\eta_s\pmod3,\qquad
(\eta_{LO},\eta_{LE},\eta_{RO},\eta_{RE})=(0,0,1,0).
\]
The canonical sector transitions are
\[
\begin{array}{c|cc}
s&L&R\\ \hline
LO&LO&RO\\
LE&LE&RE\\
RO&LE&RE\\
RE&LO&RO.
\end{array}
\]
Then
\[
\boxed{
\begin{array}{c|cc}
&L&R\\ \hline
Q'/3&D+r+1-\mathbf1_{s=RO}
&\widehat P+D+2-\mathbf1_{s=RO}\\
\widehat P'&\widehat P-r+1
&-\widehat P+r+2\mathbf1_{s\in\{LE,RO\}}
\end{array}\pmod3.}
\]

Thus the passive \(P\)-coordinate is a one-dimensional affine cocycle driven by sector, branch, and \(r\bmod3\), independent of \(D\). The active quotient \(Q'/3\) still needs both \(D\bmod3\) and \(r\bmod3\).

The remaining two-class right split cannot be removed by any sector translation: the right transitions RO→RE and RE→RO have additive constants \(2c_T(RO)+\eta_{RO}+\eta_{RE}\) and \(2c_T(RE)+\eta_{RE}+\eta_{RO}\), which differ by \(2(c_T(RO)-c_T(RE))\equiv2\pmod3\), independently of \(\eta\). The displayed \(\eta\) makes the left passive rule uniform and achieves the minimum of one left class and two right classes.

## 4. Relation to the existing root-ratio map

For \(q>0\), put
\[
x=\frac PQ=\frac{p}{3q}.
\]
If \(\rho=q/S\) with \(S=p+2q\), then
\[
\boxed{x=\frac{1-2\rho}{3\rho},\qquad \rho=\frac1{3x+2}.}
\]
So \(x=1\) is the same critical value as \(\rho=1/5\) in the existing root-ratio analysis.

The exact ratio update is
\[
x'=
\begin{cases}
\displaystyle\frac{P-Q-2T_s}{3Q+6\delta_s}
=\frac{p-3q-T_s}{3(3q+\delta_s)},&L,\\[2mm]
\displaystyle\frac{Q-P+2T_s}{3P+6\beta_s}
=\frac{3q-p+T_s}{3(p+\beta_s)},&R.
\end{cases}
\]
Suppressing the drain corrections gives
\[
x\longmapsto
\begin{cases}
(x-1)/3,&x\ge1,\\
(1-x)/(3x),&0<x<1,
\end{cases}
\]
the Möbius-conjugate form of the existing ideal tent map. The exact left-branch condition is
\[
x\ge1+\frac{T_s}{3q}.
\]
Since \(T_s=O(\ell)=O(\log q)\), this is the same logarithmic displacement of the critical boundary already present in the root-ratio dossier. This coordinate change combines the ratio and the \((p,q)\) low-digit recurrence; it does not introduce a new independent ratio map.

## 5. Exact 27-state drain-residue lift for the \((p,q)\) recurrence

The existing three-state drain transducer has states \(A,B,C\). On input digit \(d\in\{0,1,2\}\), it returns a next state \(s'\) and output digit \(o\):
\[
\begin{array}{c|ccc}
&d=0&d=1&d=2\\ \hline
A&(B,2)&(A,1)&(C,0)\\
B&(A,0)&(B,2)&(A,1)\\
C&(A,1)&(C,0)&(A,2)
\end{array}
\]

For a length-\(L\) drain word, the source digit identities give
\[
D=L-2n_2,\qquad R_{\rm full}=n_1+n_2,
\]
where \(n_i\) counts output digits \(i\). The exact mod-3 lift has state space
\[
\mathcal Q=\{A,B,C\}\times(\mathbb Z/3\mathbb Z)^2
\]
and transition
\[
(s,\bar D,\bar R)\xrightarrow{d}
\left(s',\ \bar D+1-2\mathbf1_{o=2},\
\bar R+\mathbf1_{o\ne0}\right).
\]
It starts at \((A,0,0)\). After exactly \(L\) input digits it outputs
\[
(s_L,\ D\bmod3,\ R_{\rm full}\bmod3).
\]
All 27 states are reachable; shortest access words (digits read least-significant first) are:

| State | Word | State | Word | State | Word |
|---|---|---|---|---|---|
| A00 | ε | B21 | 0 | A11 | 1 |
| C10 | 2 | A01 | 00 | B12 | 01 |
| A02 | 02 | B02 | 10 | A22 | 11 |
| C21 | 12 | A21 | 20 | C20 | 21 |
| B22 | 000 | A12 | 001 | C11 | 002 |
| B00 | 011 | A20 | 012 | B20 | 020 |
| A10 | 021 | C12 | 022 | B10 | 110 |
| C02 | 112 | C01 | 121 | C00 | 211 |
| C22 | 0012 | B11 | 0120 | B01 | 0210 |

Because the output label is the state triple itself, distinct states are immediately distinguishable. This is the exact minimal Moore state representation when the output must retain the final drain state and both residues \(D,R_{\rm full}\bmod3\).

To use the canonical \((p,q)\) table, convert \(r=R_{\rm full}-1\) in RE and \(r=R_{\rm full}\) otherwise. This 27-state lift is for the \((p,q)\) recurrence. Agent 1's corrected synchronization low-digit rule uses only \(R_{\rm full}\bmod3\), so its separate nine-state product is the appropriate smaller synchronization component.

## 6. Finite edge audit and limitations

The normalized \((p,q)\) update was checked against the materialized source-faithful edge data
im-results/agent48-623-tight-window/SWindowEdgeRecords.json. Starting from the exact D33 prefix and using each edge's \((D,R_{\rm full})\), the 9,968 transitions D33→D10001 had:
- zero source-sector or source-branch mismatches;
- zero target-sector mismatches;
- zero mismatches in either normalized \((Q'/3,\widehat P')\bmod3\) update;
- all 216 possible tuples \((s,\text{branch},D\bmod3,r\bmod3,\widehat P\bmod3)\) occurred.

The last point is a useful negative result: no exclusion follows from this one-digit \((p,q)\) residue layer alone. The finite audit is reproducible with im-results/agent27-623-root-scan/verify_sector_normalized_cocycle.js (run from the repository root with Node).

This note does **not** close the synchronization problem. Agent 1's exact synchronization coordinates are \(U=Y,V=X+Y\), with the branch corrections \(\kappa=\mathrm{corrC}\) and \(\phi=\mathrm{corrF}\) from the Lean-checked SignedCoordinateNormalForm.lean. Those corrections must be used directly; no identification of \(P=2p\) with that \(V\) is asserted here. The authentic-root drain budget, synchronization carry closure, and avoidance of the terminal strips remain open.
