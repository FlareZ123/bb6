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
