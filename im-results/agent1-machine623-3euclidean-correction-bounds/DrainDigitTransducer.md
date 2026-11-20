# Three-state ternary transducer for the exact #623 drain correction

**Status:** exact finite-state reformulation of the source drain's digit-statistic normal form. This is an intermediate research tool, not a blank-root nonhalting proof and not a BB(6) result.

## 1. The integer whose digits encode the drain

For a positive drain counter (b), let (L) be the unique integer satisfying
[
L\equiv b\pmod 2,\qquad 3^{L-1}\le 2b-1<3^{L+1}.
]
Set
[
N(b)=\frac{2b-1+3^L}{4}.
]
The parity condition makes the numerator divisible by four. The bounds give
[
3^{L-1}\le N(b)<3^L,
]
so (N(b)) has exactly (L) ternary digits.

The existing valuation normal form in `../agent41-623-3euclidean/DrainValuationNormalForm.md` gives, for a successful source drain,
[
\operatorname{drainB}(a,b,d)
=\bigl(a-L+2e,\ d+3b+2L+2\Delta\bigr),
	ag{1}
]
where (e) is the number of ternary digits of (N(b)) equal to (2), and
[
\Delta=\#\{i:n_i=1\}-\#\{i:n_i=2\}
]
for (N(b)=\sum_{i=0}^{L-1}n_i3^i). Thus the complete drain correction is determined by the base-three digits of one explicit integer.

The purpose here is to compute those digits with a **three-state transducer**, rather than by recursively executing `evalA` and `drainB` or by first materializing (N).

## 2. The three-state transducer

Read the base-three digits (b_0,b_1,\ldots,b_{L-1}) of (b) from least significant to most significant. Start in state (A). Each transition consumes one input digit (d\in\{0,1,2\}), emits one output digit (n\in\{0,1,2\}), and changes state as follows.

| State | Input 0 | Input 1 | Input 2 |
|---|---|---|---|
| (A) | (2,B) | (1,A) | (0,C) |
| (B) | (0,A) | (2,B) | (1,A) |
| (C) | (1,A) | (0,C) | (2,A) |

Each entry is ((\text{output digit},\text{next state})). After (L) transitions, the emitted digits are exactly the (L) low-to-high ternary digits of (N(b)).

Equivalently, the output digit is a state-dependent permutation of the input digit:
[
\begin{array}{c|ccc}
 &d=0&d=1&d=2\\\hline
A&2&1&0\\
B&0&2&1\\
C&1&0&2
\end{array}
]
The state update has a simple description: input digit (1) leaves the state unchanged; input digit (0) or (2) sends (A) to (B) or (C), respectively, and sends either (B) or (C) back to (A).

## 3. Derivation from ordinary carries

Write (c_i) for the ternary digits of (2b-1). Its low-to-high multiplication/subtraction carry (u_i) satisfies
[
u_0=-1,\
2b_i+u_i=c_i+3u_{i+1}.
	ag{2}
]
To solve (4N= N+3N\equiv 2b-1\pmod{3^L}), let (n_{-1}=0) and use the carry (v_i) in the addition (N+3N):
[
v_0=0,\
n_i+n_{i-1}+v_i=c_i+3v_{i+1}.
	ag{3}
]
For fixed ((u_i,n_{i-1},v_i)) and input (b_i), equations (2)–(3) uniquely determine (c_i,u_{i+1},n_i,v_{i+1}). Starting from ((-1,0,0)), only eight carry triples are reachable. They fall into three output-equivalence classes:
[
egin{aligned}
A&=\{(-1,0,0),(0,1,0),(1,1,1),(1,2,0),(0,0,1)\},\\
B&=\{(-1,2,0),(0,2,1)\},\\
C&=\{(1,0,0)\}.
end{aligned}
]
Within each class, every input digit gives the same output digit and the same successor class. Quotienting the eight carry triples therefore gives exactly the table in Section 2. The three quotient states are distinguishable: on input (0), their outputs are (2,0,1), respectively.

Equations (2)–(3) prove the digit claim by induction on the processed prefix. After (i) positions, the emitted prefix is the unique solution to
[
4N\equiv 2b-1\pmod{3^i}.
]
Since (4) is a unit modulo (3^i), the low (i) digits are uniquely determined. At (i=L), (0\le N<3^L), so the emitted word is exactly (N(b)), not merely a congruent representative.

## 4. Drain corrections are additive transducer weights

For each emitted digit (n_i), attach the weights
[
\begin{array}{c|ccc}
n_i&0&1&2\\\hline
\text{contribution to }R&0&1&1\\
\text{contribution to }e&0&0&1\\
\text{contribution to }\Delta&0&1&-1
\end{array}
]
Then (R=\#\{i:n_i\ne0\}), (e=\#\{i:n_i=2\}), and (Delta=\sum_i\Delta_i). The exact whole-drain normal form is therefore obtained in one left-to-right pass over the ternary digits of (b):
[
D=L-2e,\qquad
\operatorname{drainB}(a,b,d)
=\bigl(a-D,\ d+3b+2D+2R\bigr),
]
which is (1).

For the four canonical #623 rays, the drain counter (b) is:
- left-odd: (b=q+3);
- left-even: (b=q+2);
- right-odd: (b=q-1);
- right-even: (b=q+1), with the initial evaluator absorbed into the full-drain convention.

Thus the exact correction data for each canonical root transition are a three-state weighted transduction of the ternary digits of (q+c), with (c\in\{3,2,-1,1\}). This exposes the recursive drain correction as a small deterministic digit process.

## 5. Reproducibility and research use

`drain_digit_transducer.js` is a dependency-free BigInt reference implementation. It verifies the identity (4N=2b-1+3^L) and the three accumulated digit statistics for (1\le b\le10{,}000). The proof is the carry derivation above; the finite replay is only an implementation check.

The useful next composition is with the existing two-coordinate carry transducer and the moving-window boundary state from `../agent41-623-3euclidean/MonotoneMassWindow.md`. The drain's entire recursive history can be replaced by:
1. the three-state transducer state at the low ternary boundary;
2. the accumulated weights (R,e,\Delta);
3. the parity-adjusted digit length (L).

This may make the authentic-root boundary-carry closure a smaller finite-state problem. It does **not** establish that the root orbit avoids the terminal strips; the all-time root-history invariant remains open.


## 6. A compact state-offset and weighted form

Assign the state offsets
\[
s_A=2,\qquad s_B=0,\qquad s_C=1.
\]
The output digit in every transition is simply
\[
n_i\equiv s_i-b_i\pmod3,
\]
with its representative in \(\{0,1,2\}\). The state update can be read directly from the table: an input 1 leaves the state unchanged; an input 0 or 2 toggles between A and a non-A state, with the non-A state recording whether the last such input was 0 (B) or 2 (C). Equivalently, A occurs after an even number of non-1 input digits; B/C occurs after an odd number, with the most recent non-1 digit distinguishing B from C.

This gives immediate interpretations of the digit statistics:
\[
R=\#\{i:b_i\ne s_i\},\qquad
e=\#\{i:b_i\equiv s_i+1\pmod3\}.
\]
The mass and branch-threshold corrections have especially simple per-digit weights. If \(\mu(n)=2\) for \(n=1\) and 0 otherwise, and
\[
\theta(0)=0,\quad\theta(1)=2,\quad\theta(2)=-4,
\]
then, with the sector constants \(c_s=(9,6,4,4)\) and \(c_T=(19,10,-4,2)\) in LO/LE/RO/RE,
\[
\boxed{\eta=\beta+\delta=L+c_s+\sum_i\mu(n_i)}
\]
and
\[
\boxed{T=3D+2R+c_T=3L+c_T+\sum_i\theta(n_i).}
\]
Thus the same three-state pass computes both the exact total-mass increment and the exact output-side threshold.

There is also a small sharpening of the mass-indexed window bound. If \(\ell_S\) is least with \(S+3\le\tau(\ell_S)\), then \(q+3\le S+3\le\tau(\ell_S)\). Each canonical drain parameter satisfies \(b\le q+3\), so
\[
2b-1<3^{\ell_S}.
\]
The defining lower bound \(3^{L-1}\le2b-1\) therefore gives \(L\le\ell_S\). Since \(\sum_i\mu(n_i)\le2L\) and \(c_s\le9\),
\[
\eta\le3L+9\le3\ell_S+9.
\]
Using \(q\le S/2\) and the existing \(\ell_S\le S/2-1\) estimate for \(S\ge20\), the exact mass recurrence \(S'=S+q+\eta\) improves the previous coarse upper bound to
\[
\boxed{S'\le3S+6.}
\]
This does not change the established \(\ell_{S'}-\ell_S\in\{0,1\}\) conclusion, but gives a sharper source-independent growth envelope.


## 7. Exact affine carry corrections from the same digit stream

The source-checked SignedCoordinateNormalForm.lean gives the affine corrections C,F in the integer coordinates x=2g-gamma_s, y=6q. Substituting D=L-2e, R=n_1+n_2, where n_j is the number of output digits equal to j, turns those corrections into the following weighted digit sums.

For a left output:
\[
C=-18L-16n_1+20n_2+c_C,\qquad
F=12L+12n_1-12n_2+c_F.
\]
For a right output:
\[
C=12L+4n_1-20n_2+c_C,\qquad
F=-6L+12n_2+c_F.
\]
The sector/output constants are exactly:

| Sector | Output | c_C | c_F |
|---|---|---:|---:|
| LO | L | -122 | 84 |
| LE | L | -68 | 48 |
| RO | L | 0 | 0 |
| RE | L | -36 | 18 |
| LO | R | -6 | 24 |
| LE | R | -12 | 18 |
| RO | R | -44 | 30 |
| RE | R | -20 | 18 |

These formulas are obtained directly from corrC and corrF in SignedCoordinateNormalForm.lean; no simulation is involved. Since n_1,n_2 >= 0 and n_1+n_2 <= L, they imply the uniform bounds
\[
|C|\le34L+122,\qquad |F|\le24L+84.
\]
For the q-depth ell used by the carry scan, b <= q+3 <= tau(ell), so L <= ell; the same argument gives L <= ell_S for the mass depth. Thus the correction-only scan buffer can be reduced to 34 ell+122. If the centered terminal window is also included, the combined scan parameter becomes
\[
B_{new}=\max(34\ell_S+122,\ 36\ell_S+88),
\]
instead of the previous max(34 ell_S+140,36 ell_S+88). The combined bound is strictly smaller than the previous one for ell < 26 and agrees with it for ell >= 26.

There is a useful interpretation of the observed actual-boundary-carry rectangles. If the low residue lies in [0,3K) and |C|,|F|<K, then:
- C <= 0 forces the first carry into {-1,0};
- C >= 0 forces the first carry into {0,1};
- F >= 0 forces the second carry into {0,1};
- F <= 0 forces the second carry into {-1,0}.

Thus the empirical root pattern (left output: first carry nonpositive, second nonnegative; right output: first nonnegative, second nonpositive) is exactly the sign pattern
\[
L:\ C\le0\le F,\qquad R:\ F\le0\le C.
\]
The sign pattern is not a consequence of the cone hypotheses alone: the weighted formulas show that it depends on the root's digit statistics n_1,n_2. But it is now an explicit finite-state weighted condition on the same three-state drain scan. This is a direct interface for the boundary-carry closure: compute the digit weights, then the exact C,F, then the actual boundary carry pair.


The inequalities above are now formalized by correction_count_bounds and correction_buffer_closed in SignedCoordinateNormalForm.lean, using \(E=n_2\le R=n_1+n_2\le L\). The companion theorem one_extra_digit_carry_bound_closed allows \(|c|\le K\), not merely \(|c|<K\). Therefore \(K=34L+122\) bounds both corrections and is sufficient for the correction-only carry bound even when \(C\) attains equality; an extra additive margin is unnecessary. This controls only the additive correction quotient, not the total boundary carry: the base residue quotient must be combined before asserting an actual start-carry rectangle (see Agent 49's CarryBoundAudit.md, root index 38).

## 8. The valid-length terminal state and exact carry invariant

There is a compact integer invariant behind the three-state machine. Assign
\[
\kappa(A)=1,\qquad \kappa(B)=3,\qquad \kappa(C)=-1.
\]
For every transition \(s\xrightarrow{d/n}s'\), the nine entries of the table satisfy
\[
\boxed{3\kappa(s')=\kappa(s)+4n-2d.}
\]
If \(b_i,N_i\) are the low-\(i\)-digit input and output prefixes and \(s_i\) is the state after those digits, induction gives
\[
4N_i-2b_i+\kappa(s_0)=3^i\kappa(s_i).
\]
Starting in A, this is \(4N_i-2b_i+1=3^i\kappa(s_i)\).

The upper size condition \(2b-1<3^{L+1}\), together with \(3^L\ge1\), implies \(b<2\cdot3^L\); hence the leading ternary digit \(h=\lfloor b/3^L\rfloor\) is in \(\{0,1\}\). Now write the full input as \(b=b_0+h3^L\), with \(0\le b_0<3^L\). The parity condition \(L\equiv b\pmod2\), together with \(3^i\equiv1\pmod2\), shows that the number of 1-digits among the low L digits has parity \(b_0\). Hence the number of non-1 digits has parity \(L+b_0\equiv h\pmod2\), so it is even when \(h=0\) and odd when \(h=1\). Since each input digit 0 or 2 toggles A versus the non-A states, while digit 1 leaves that phase unchanged:
- \(h=0\) forces terminal state A;
- \(h=1\) forces terminal state B or C.

The C possibility is excluded by the upper size condition \(2b-1<3^{L+1}\). If the terminal state were C, the carry identity would give
\[
4N=2b-1-3^{L+1}<0,
\]
contradicting the nonnegative emitted integer. Thus the terminal state is exactly
\[
\boxed{\text{A if }b<3^L,\qquad \text{B if }b\ge3^L.}
\]
Equivalently, \(\kappa(s_L)=1+2h\). Substitution into the carry identity yields the exact formula
\[
\boxed{4N=2b-1+3^L.}
\]
This proof uses only the transition identity, parity, the upper size bound, and nonnegativity of emitted digits; it does not assume the desired output formula in order to establish the terminal state.

## 9. Lean formalization and exact interface

The standalone Lean 4.36.0-rc2 proof is in [DrainDigitTransducerCarry.lean](DrainDigitTransducerCarry.lean). It uses only Lean core imports; no Mathlib dependency is required. An axiom audit of the principal theorems reports only Lean core axioms (propext, Quot.sound, Classical.choice); there is no sorryAx dependency.

The module formalizes:
- the nine one-step carry identities;
- the recursive carry invariant for every input word and every initial state;
- the phase/parity invariant;
- nonnegativity and the \(3^L\) output bound;
- the exact output formula, including the direct theorem drain_transducer_exact_of_bounds;
- runStats, which retains the output-1 and output-2 counts and proves \(0\le n_2\le n_1+n_2\le L\). These give the weighted statistics \(E=n_2\), \(R=n_1+n_2\), and \(D=L-2E\) consumed by SignedCoordinateNormalForm.lean. The Lean definitions weightedE, weightedR, weightedD and theorem runStats_weight_bounds expose the exact nonnegative count inequalities required by correction_buffer_closed. The terminal phase is also exposed by runStats_phase_of_decomposition: under the same low/high decomposition and parity condition, phaseBit(finalState)=high. Here E is the output-2 digit count used in the affine correction formulas; it is not the second counter E returned by the separate root drainB recurrence in GapScaleResidualSource.lean. Likewise runStats is the digit transducer interface, not a replacement for the root's drainB.

**Canonical-ray hypotheses.** In the source application, \(b\) is the positive drain parameter and \(L\) is the parity-adjusted ternary length. The canonical interval is
\[
3^{L-1}\le 2b-1<3^{L+1},\qquad L\equiv b\pmod2.
\]
The theorem drain_transducer_exact_canonical accepts exactly these hypotheses and proves
\[
4N=2b-1+3^L,
\]
where \(N\) is the output from runStats on the low \(L\) ternary digits \(b\bmod 3^L\). The lower inequality records the canonical length choice; the stronger drain_transducer_exact_of_bounds theorem needs only the parity and upper inequality.

**Scope boundary.** This interface proves the drain transducer identity and its weighted outputs for supplied \((b,L)\). It does not prove that a particular \((b,L)\) occurs on the authentic D(0,7) root orbit, nor does it determine the total boundary carry. The latter must include the base linear quotient as well as the additive correction quotient; see Agent 49's CarryBoundAudit.md.
