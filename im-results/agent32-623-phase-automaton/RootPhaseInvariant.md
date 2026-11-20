# Candidate source-level #623 root phase invariant

**Status:** explicit induction target and failure boundary, not a theorem. This document consolidates the root-window, reset-DFA, actual-carry, sector, and drain interfaces. The canonical source-faithful root trace remains [Agent 27's diagnostic](../agent27-623-root-scan/README.md).

## 1. Exact root coordinates and finite prefix

For a section state (D(a,d)), set
[
q=min(a,d),quad p=|a-d|,quad g=p-3q,quad
S=p+2q=a+d,
]
and in sector (sin{LO,LE,RO,RE}) set
[
gamma_{LO}=18,quadgamma_{LE}=10,quad
gamma_{RO}=2,quadgamma_{RE}=4,quad
x=2g-gamma_s,quad y=6q.
]

The exact root prefix begins
[
D(0,7),D(6,14),D(6,31),D(26,26),D(2,83),D(84,10),ldots
]
and the source-connected `newAffineCone` is observed from index 9 onward in the existing 20k source-faithful replay. The finite prefix must be proved directly from the pinned source before using any invariant.

## 2. Moving central window

Let (ell(q)) be the least integer with (ell(ell+1)/2ge q+3), and
[
B(ell)=max(34ell+122,36ell+88).
]
Let (k) be least with (3^k>B(ell)), and (j) least with (3^j>B(ell)^3). The digit-pair word is
[
W(D(a,d))=((x_i,y_i):k+1le ile j-3).
]
The exact window changes satisfy (k'-kin{0,1}), (j'-jin{0,1,2,3}). If (U) is the branch-transducer output on the current word, the next word is obtained by the exact low shift and at most three high extension symbols. The shift is not optional: a reset pattern in an arbitrary suffix of (U) does not prove that the next whole window is reset.

## 3. Reset recognizer and what it proves

[ResetPatternDFA.json](ResetPatternDFA.json) is the 263-state minimal DFA for words containing a common reset pattern of length 3--6. It was constructed from 29,445 substring-minimal common patterns. The corresponding complete transducer states after any minimal reset pattern are only:
- L: 18 states (all 9 final digit pairs, carries ((-1,0)) or ((0,0)));
- R: 36 states (all 9 final digit pairs, carries ((-3,1),(-2,0),(-2,1),(-1,0))).

Thus if (W_n) contains a common reset pattern, the transducer carry after that pattern has a finite 18/36-state phase. This gives a finite post-reset suffix computation.

**Important falsification:** the reset language alone is not preserved by either raw branch transducer. The exact length-3 witnesses are in [ClosureCounterexample.md](ClosureCounterexample.md). Adding only input-x nonmonochromaticity and even restricting to the observed actual boundary phase set still admits arbitrary-word counterexamples. These do not refute the authentic root, but they prove that the reset DFA and carry set alone are not an invariant. The authentic root's 3-adic prefix constraints must be retained.

## 4. Actual boundary phase

The carry entering digit (k+1) is determined by the exact correction (C,F) and low residues. Write (K=3^k). The formulas are:
- L:
  [
  a=leftlfloorrac{x_{<k+1}-3y_{<k}+C_L}{3^{k+1}}ightfloor,qquad
  b=leftlfloorrac{3y_{<k}+F_L}{3^{k+1}}ightfloor.
  ]
- R:
  [
  a=leftlfloorrac{-x_{<k+1}-3x_{<k}-3y_{<k}+C_R}{3^{k+1}}ightfloor,qquad
  b=leftlfloorrac{3x_{<k}+3y_{<k}+F_R}{3^{k+1}}ightfloor.
  ]

Here (C,F) are obtained from the parity-correct drain length and digit counts using the source correction table. The previous pair is ((x_k,y_k)). The exact extraction over indices 33--10,000 is recorded in [ActualBoundaryPhases.md](ActualBoundaryPhases.md) and [ActualBoundaryPhases.json](ActualBoundaryPhases.json):
- 262 observed complete phases (114 L, 148 R);
- actual L carry pairs ((-2,1),(-1,0),(-1,1),(0,0));
- actual R carry pairs ((-3,1),(-2,0),(-2,1),(-1,-1),(-1,0),(-1,1),(0,0));
- zero affine-update mismatches and zero sector-transition mismatches on the diagnostic interval.

The 262 observed phases are **not** a proved invariant and are not deterministic by themselves: the observed transition relation has maximum outdegree 25.

## 5. Sector and branch phase

The source parity table and the sign-based branch-selection lemma give:
[
egin{array}{c|cc}
s&g>0;(L)&g<0;(R)\hline
LO&LO&RO\
LE&LE&RE\
RO&LE&RE\
RE&LO&RO
end{array}
]
This recovers the eight observed edges but does not prove that no other branch of `highLevelNext` can occur. Branch completeness must be proved from the candidate invariant, not inferred from the finite trace.

## 6. Candidate invariant to prove

The intended root-history invariant has the following components, for every state after the exact finite prefix:
1. **Cone:** the state lies in the source-connected `newAffineCone`, so every subsequent section transition exists and the existing quadratic-gain theorem applies.
2. **Sector:** the state has one of the four canonical sector labels; the exact branch/sector update table above is exhaustive.
3. **Boundary:** the actual ((x_k,y_k,a_{k+1},b_{k+1})) lies in a proved finite boundary-phase set (the 262 observed phases are a candidate, not an accepted set).
4. **Root prefix language:** the authentic central word (W_n) lies in a source-derived regular/weighted language (\mathcal L_{root}) that implies acceptance by the 263-state reset DFA within the first 13 symbols. The raw arbitrary-word counterexamples show (\mathcal L_{root}) must be strictly smaller than “reset + x-nonmonochromatic”.
5. **Drain interface:** the parity-correct 3-state low-to-high drain transducer, its weighted outputs (D,R), and the sector-dependent correction (C,F) are composed with the coordinate transducer. The required state must retain enough weighted information to compute the next boundary phase; the terminal drain state/last output alone is insufficient.
6. **Window shift:** the exact ((\delta,\eta)=(k'-k,j'-j)) update and high extension are included. The next whole word, not an arbitrary suffix, must be accepted.

If these clauses close, reset acceptance gives the next central (x)-block nonmonochromatic. The existing middle-block residue certificate then gives (|x|>B(ell)), while the terminal-strip bridge gives (|x|le B(ell)) for a terminal successor. This contradiction rules out terminal successors and composes with the original-machine root semantics.

## 7. Concrete proof obligations

- Prove the finite prefix from (D(0,7)) into the invariant using the pinned original recurrence.
- Prove the four-sector branch partition is exhaustive inside the invariant; explicitly exclude exceptional branches such as (a=0), the odd-(a) stop branch, and the equality branch when applicable.
- Derive the authentic prefix language (\mathcal L_{root}) from the exact (p,q) recurrence / 3-adic cocycle; do not fit it only to the finite scan.
- Prove the drain/coordinate product and actual boundary-phase update, including all low/high shifts.
- Prove the reset-DFA acceptance transition for every reachable product phase.
- Prove the invariant implies `newAffineCone` and the existing terminal-strip contradiction.
- Compile the full theorem against unchanged original source and inspect the exported transitive axiom profile.

## 8. Rejected shortcuts

- The 8-edge sector graph is observed, not branch-complete.
- A scalar gap/slack bound is not forward-invariant for arbitrary states; retain the known counterexamples (D(18,88)\to D(70,65)) and (D(2,69)\to D(70,10)) as regression tests.
- The reset DFA alone, reset plus input-x nonmonochromaticity, and the observed actual carry set alone all fail on synthetic arbitrary words.
- Do not extend the root scan horizon, create another scan implementation, or promote an observed phase set to an all-time theorem.
