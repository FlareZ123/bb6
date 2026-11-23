# Sector-normalized two-register cocycle and drain residues

**Status:** exact algebraic reduction of the source-derived canonical-ray map, plus a finite-state residue lift. It is not a root invariant, a halting/nonhalting proof, or a BB(6) result. Kept in im-results because the source-to-root closure is still open.

This note refines Agent 1's TwoCoordinate3AdicCocycle.md by removing the sector offsets from the second register. It also identifies the exact finite automaton needed to supply the drain statistics modulo 3.

## 1. Sector-normalized coordinates

Use the canonical-ray coordinates
\[
p=|a-d|,\qquad q=\min(a,d),
\]
and the exact sector correction table
\[
A=p+\beta_s,\qquad E=3q+\delta_s,\qquad
p'=|A-E|,\quad q'=\min(A,E).
\]
Let \(T_s=\delta_s-\beta_s\). The output is left-oriented when \(p-3q\ge T_s\), and right-oriented otherwise.

Agent 1's coordinates are \(U=6q\), \(V=2p-\gamma_s\), where
\[
(\gamma_{LO},\gamma_{LE},\gamma_{RO},\gamma_{RE})=(18,10,2,4).
\]
Define instead
\[
\boxed{U=6q,\qquad W=2p=V+\gamma_s.}
\]
The second coordinate is translated by the current sector, so this is a sector-adapted coordinate, not a single global linear map.

Substitution into the exact \((p,q)\) branches gives the following **integer identities**:

**Left output** (\(p'=p-3q-T_s,\ q'=3q+\delta_s\)):
\[
\boxed{U'=3U+6\delta_s,\qquad W'=W-U-2T_s.}
\]

**Right output** (\(p'=3q+T_s-p,\ q'=p+\beta_s\)):
\[
\boxed{U'=3W+6\beta_s,\qquad W'=U-W+2T_s.}
\]

Unlike the \((U,V)\) form, these equations contain no \(\gamma_s'\). The target-sector phase is needed only to interpret the next state's sector and to select its next drain input.

## 2. Exact mod-3 quotient table

Use Agent 1's drain convention:
\[
\begin{array}{c|rrr}
s&\beta_s&\delta_s&T_s\\ \hline
LO&-D-5&2D+2r+14&3D+2r+19\\
LE&-D-2&2D+2r+8&3D+2r+10\\
RO&4-D&2D+2r&3D+2r-4\\
RE&1-D&2D+2r+5&3D+2r+4
\end{array}
\]
Here \(D\) is the signed drop, and \(r\) counts subsequent drain iterations. In RE only, the full evaluator-call count used by Agent 48 is \(R=r+1\); in the other sectors \(R=r\). Thus when consuming Agent 48's edge records, convert \(r=R-\mathbf1_{s=RE}\). The signed drop \(D\) already includes the initial RE evaluator.

Since \(U=6q\equiv0\pmod3\), dividing the active register by 3 gives
\[
\begin{array}{c|cc}
&\text{left output}&\text{right output}\\ \hline
U'/3&D+r+2c_\delta(s)&W+D+2c_\beta(s)\\
W'&W-r-2c_T(s)&-W+r+2c_T(s)
\end{array}\pmod3
\]
where \(c_\beta=(-5,-2,4,1)\), \(c_\delta=(14,8,0,5)\), and \(c_T=(19,10,-4,4)\) in sector order LO, LE, RO, RE.

In particular \(2c_\beta(s)\equiv2\) in every sector. The full table is therefore
\[
\begin{array}{c|cc}
s&\text{left output }(U'/3,W')&\text{right output }(U'/3,W')\\ \hline
LO&(D+r+1,\ W-r+1)&(W+D+2,\ -W+r+2)\\
LE&(D+r+1,\ W-r+1)&(W+D+2,\ -W+r+2)\\
RO&(D+r,\ W-r+2)&(W+D+2,\ -W+r+1)\\
RE&(D+r+1,\ W-r+1)&(W+D+2,\ -W+r+2)
\end{array}\pmod3.
\]

This table separates the two drain statistics: the passive register \(W'\bmod3\) depends on \(r\bmod3\), but not on \(D\bmod3\); the active quotient \(U'/3\bmod3\) needs \(D\bmod3\) as well.

## 3. A normalized passive register

The remaining sector dependence in the passive update can be reduced further. Put
\[
\widehat W=W+\eta_s\pmod3,\qquad
(\eta_{LO},\eta_{LE},\eta_{RO},\eta_{RE})=(0,0,1,0).
\]
Use the exact canonical sector transition table
\[
\begin{array}{c|cc}
s&L&R\\ \hline
LO&LO&RO\\
LE&LE&RE\\
RO&LE&RE\\
RE&LO&RO
\end{array}
\]
(the choice of L/R for an authentic root step remains conditional on the nonterminal/central-block hypothesis in the existing branch-selection result).

The update becomes
\[
\boxed{
\begin{array}{c|cc}
&L&R\\ \hline
U'/3&D+r+1-\mathbf1_{s=RO}
&\widehat W+D+2-\mathbf1_{s=RO}\\[1mm]
\widehat W'&\widehat W-r+1
&-\widehat W+r+2\mathbf1_{s\in\{LE,RO\}}
\end{array}\pmod3.}
\]

Thus the passive register has one uniform left rule and only a two-class right rule. The active quotient still distinguishes RO from the other three sectors. This is a substantially smaller phase dependence than the unnormalized \((U,V)\) expression, but it is not a closed root automaton: the next \(D,r\) must be computed from the next state's complete canonical drain.

There is a small cohomological obstruction behind the remaining right split. If one tries a general sector translation \(W+\eta_s\) and demands a single sector-independent additive constant for *both* passive branch updates, the left equations force
\[
\eta_{RO}-\eta_{LE}=1,\qquad \eta_{RE}=\eta_{LO}\pmod3.
\]
The right transitions LO→RO and LE→RE then have constants differing by 2 modulo 3. Hence no sector translation can make both branch constants uniform. The displayed \(\eta\) attains the minimum total of three additive classes (one on L, two on R).

## 4. Exact 27-state drain-residue lift

The pinned three-state drain transducer in
im-results/agent1-machine623-3euclidean-correction-bounds/DrainDigitTransducerCarry.lean
has states \(A,B,C\). For input digit \(d\in\{0,1,2\}\), it returns a next state \(s'\) and output digit \(o\):
\[
\begin{array}{c|ccc}
&d=0&d=1&d=2\\ \hline
A&(B,2)&(A,1)&(C,0)\\
B&(A,0)&(B,2)&(A,1)\\
C&(A,1)&(C,0)&(A,2)
\end{array}
\]

For a length-\(L\) drain word, \(D=L-2n_2\) and \(r=n_1+n_2\), where \(n_i\) counts output digits \(i\). The exact mod-3 lift has state space
\[
\mathcal Q=\{A,B,C\}\times(\mathbb Z/3\mathbb Z)^2
\]
and transition
\[
(s,\bar D,\bar r)\xrightarrow{d}
\left(s',\ \bar D+1-2\mathbf1_{o=2},\
\bar r+\mathbf1_{o\ne0}\right).
\]
It starts at \((A,0,0)\). After exactly \(L\) input digits its output is
\[
(s_L,\ D\bmod3,\ r\bmod3).
\]
This is an exact finite-state projection of runStats, not a fitted root-trace model.

A breadth-first construction reaches all 27 states. Shortest access words (digits are read least-significant first) are:

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

The output label is the state triple itself, so distinct states are immediately distinguishable as a Moore machine. This 27-state lift is therefore the exact minimal state representation if the output must retain \((s_L,D\bmod3,r\bmod3)\).

For RE inputs, the residue needed in the preceding tables is \(r=R-1\); the automaton naturally produces the full count \(R\) when run with the full evaluator-call convention, so apply that one-unit conversion at the RE interface.

## 5. What this closes, and what it does not

The algebraic reduction gives a compact candidate low-digit layer:
\[
(s,\text{branch},D\bmod3,r\bmod3,\widehat W\bmod3)
\longmapsto
(s',\,U'/3\bmod3,\,\widehat W'\bmod3).
\]
The 27-state drain lift supplies the two statistic residues from the exact low-\(L\)-digit drain word. The separate S-window boundary carry is still necessary for the higher digits and for the exact next-window quotient. In particular, the central window alone does not determine the complete next drain word; do not claim closure by composing only these mod-3 states.

I checked the displayed normalized update against the materialized source-faithful edge data im-results/agent48-623-tight-window/SWindowEdgeRecords.json. Starting from the exact D33 prefix and using each edge's exact \((D,R)\), the 9,968 transitions D33→D10001 had:
- zero source-sector or source-branch mismatches;
- zero target-sector mismatches;
- zero mismatches in either normalized mod-3 output;
- all 216 possible tuples \((s,\text{branch},D\bmod3,r\bmod3,\widehat W\bmod3)\) occurred.

The last point is a useful negative result: no exclusion follows from this one-digit residue layer alone. The remaining proof-relevant target is to compose the 27-state drain lift with the **full** source-derived boundary carry and the authentic S-window shift/high-extension map, then prove closure or find an exact counterexample. The 1,318 phase cores must not be treated as Markov states; the per-edge drain/window fields in SWindowEdgeRecords.json remain essential.

No Lean compilation or original-machine nonhalting theorem is claimed here.
