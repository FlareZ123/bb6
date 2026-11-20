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


## 6. Compact state-offset and weighted form

Assign the state offsets
\[
s_A=2,\qquad s_B=0,\qquad s_C=1.
\]
The output digit in every transition is
\[
n_i\equiv s_i-b_i\pmod3,
\]
with its representative in \(\{0,1,2\}\). The state update is the finite three-state rule in Section 2.

Use distinct names for the digit statistics:
\[
R_{\rm dig}=n_1+n_2,\qquad E_{\rm dig}=n_2,\qquad
\Delta=n_1-n_2=R_{\rm dig}-2E_{\rm dig}.
\]
These are computed by the transducer; its theorem runStats_weight_bounds proves
\(0\le E_{\rm dig}\le R_{\rm dig}\le L\).

The digit-side expressions are
\[
\eta_{\rm dig}=L+c_s+2n_1,\qquad
T_{\rm dig}=3L+c_T+2n_1-4n_2,
\]
where \(c_s=(9,6,4,4)\) and \(c_T=(19,10,-4,2)\) in LO/LE/RO/RE. These are finite-state weighted outputs of the transducer.

**Source-statistic distinction.** The original-root cocycle in RootRayGapCocycle.md and SignedCoordinateNormalForm.lean uses \(R_{\rm full}\), the actual number of evaluator calls in the complete drain; in RE it includes the initial evaluator. Its exact threshold is
\[
T_{\rm full}=3D+2R_{\rm full}+c_T.
\]
The equalities \(D=L-2E_{\rm dig}\) and \(R_{\rm full}=R_{\rm dig}\) are the intended bridge from the digit transducer to the source drain. The valuation expansion in DrainValuationNormalForm.md derives them on paper, including one nonzero digit per drain iteration, but the complete original-source bridge has not yet been compiled as a theorem. Until it is, \(T_{\rm dig}\) and \(\eta_{\rm dig}\) are candidate source expressions, not source-certified root-cocycle values. In particular, do not use runStats_weight_bounds as a proof about \(R_{\rm full}\).

The mass estimate \(\eta_{\rm dig}\le3L+9\) follows immediately from \(n_1\le L\). If the source bridge is established, then with \(L\le\ell_S\), \(q\le S/2\), and the existing \(\ell_S\le S/2-1\) estimate for \(S\ge20\), the source mass recurrence gives the candidate bound
\[
S'\le3S+6.
\]
The last recurrence application remains conditional on the source bridge.

## 7. Exact affine carry corrections and depth buffers

The source-checked signed-coordinate table takes two **source** parameters: the signed first-counter drop \(D\), and \(R_{\rm full}\), the full number of evaluator calls. Its corrC and corrF definitions must not silently receive \(R_{\rm dig}=n_1+n_2\) unless the source bridge in Section 6 has been proved.

If the bridge \(D=L-2E_{\rm dig}\), \(R_{\rm full}=R_{\rm dig}\) holds, substitution gives the weighted digit formulas:

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
The sector/output constants remain:

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

The following two arithmetic theorems separate what is already available from what still needs the digit/source bridge:

1. **correction_buffer_from_depth** assumes only the actual full-drain bounds
   \[
   -\ell\le D\le\ell+1,\qquad 0\le R_{\rm full}\le\ell,
   \]
   and proves
   \[
   |C|\le34\ell+140,\qquad |F|\le24\ell+96.
   \]
   This is the conservative buffer justified by the existing source depth package, without identifying digit counts with source evaluator calls.

2. **correction_buffer_by_depth** assumes
   \[
   D=L-2E_{\rm dig},\quad 0\le E_{\rm dig}\le L\le\ell,
   \quad 0\le R_{\rm full}\le\ell,
   \]
   and proves
   \[
   |C|\le34\ell+122,\qquad |F|\le24\ell+84.
   \]
   Crucially, this theorem does **not** require \(E_{\rm dig}\le R_{\rm full}\) or \(R_{\rm full}\le L\). It avoids the overloaded-\(R\) inference in the earlier note. The remaining condition is the exact source identity \(D=L-2E_{\rm dig}\).

The source depth wrapper in RootRayDrainDepthSource.lean supplies \(R_{\rm full}\le\ell\) and \(D\in[-\ell,\ell+1]\); the size inequality gives \(L\le\ell\), and the transducer gives \(0\le E_{\rm dig}\le L\). Thus the conservative \(34\ell+140\) correction bound is available from the source depth package. The sharper \(34\ell+122\) bound is conditional on the uncompiled digit/source identity for \(D\).

Agent 48's sector-specific terminal-window estimates give output-coordinate bounds
\[
12\ell+88,\quad12\ell+62,\quad12\ell+38,\quad18\ell+50
\]
in LO/LE/RO/RE. Each is below \(34\ell+140\) for \(\ell\ge0\). Consequently the separate \(36\ell+88\) terminal term is unnecessary if that terminal-window wrapper is accepted; the presently safe combined buffer is \(B_{\rm safe}=34\ell+140\). Use \(34\ell+122\) only after the source digit bridge is proved. The S-window diagnostic must be rerun with the chosen buffer; the earlier 9,968/9,968 result for the smaller conditional buffer does not establish acceptance for \(B_{\rm safe}\).

Finally, one_extra_digit_carry_bound_closed bounds only the **additional correction quotient**. It does not bound the total carry after the base linear quotient is included. Agent 49's authentic root-index-38 carry \((-2,0)\) remains a counterexample to the small \([-1,1]^2\) start set. Keep the full justified carry rectangles: L \([-2,2]\times[-2,2]\), R \([-4,1]\times[-2,2]\).

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

The standalone Lean 4.36.0-rc2 proof is in DrainDigitTransducerCarry.lean. It uses only Lean core imports; no Mathlib dependency is required. The principal arithmetic theorems have only standard Lean core axioms and no sorryAx.

The module formalizes:
- the nine one-step carry identities;
- the recursive carry invariant for every input word and every initial state;
- the phase/parity invariant;
- nonnegativity and the \(3^L\) output bound;
- the exact output formula, including drain_transducer_exact_of_bounds;
- runStats, which proves only the digit-statistic inequalities
  \(0\le E_{\rm dig}\le R_{\rm dig}\le L\), with
  \(E_{\rm dig}=n_2\) and \(R_{\rm dig}=n_1+n_2\).

It does **not** import the original evalA/drainB definitions or prove that \(R_{\rm dig}\) equals the full source evaluator-call count. Nor does it prove that the source first-counter drop is \(L-2E_{\rm dig}\) for the authentic bundled canonical ray. Those are the remaining source-bridge obligations.

The arithmetic correction lemmas correction_buffer_from_depth and correction_buffer_by_depth are in SignedCoordinateNormalForm.lean. They are self-contained integer proofs; I locally compiled their exact definitions and proof terms with Lean 4.36.0-rc2. The former uses the source depth bounds as hypotheses; their combined original-source wrapper remains pending pinned CI. The latter is additionally conditional on the digit formula for D.

**Canonical-ray hypotheses.** For a supplied positive drain parameter \(b\), the transducer accepts \(L\) under
\[
3^{L-1}\le2b-1<3^{L+1},\qquad L\equiv b\pmod2,
\]
and proves its output integer \(N\) satisfies
\[
4N=2b-1+3^L.
\]
This is an arithmetic statement about supplied \((b,L)\), not a theorem that the authentic root's source drain has the same \(D,R\) statistics.

**Scope boundary.** The transducer identity, digit weights, and correction bounds do not prove that a particular \((b,L)\) occurs on the authentic \(D(0,7)\) orbit, nor do they bound the total boundary carry. The latter must include the base linear quotient as well as the additive correction quotient; see Agent 49's CarryBoundAudit.md.
