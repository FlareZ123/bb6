# Even-length standalone-F runs in the signed branch-29 inverse system

**Status:** exact hand proof from the compressed signed rules; not yet formalized in Lean. This is an intermediate structural reduction, not a branch-29 closure or a source-machine theorem.

## Setup

Use the compressed signed state ((u,D)) and blocks from [Agent 22's signed-drift analysis](../agent22-429-signed-drift/README.md):

- (F:(u,D)\mapsto(u/2,D+3u+3)), when (u) is even;
- (EF:(u,D)\mapsto(u+(D+8)/8,D/4+4)), when (u) is odd and (8\mid D);
- (SF:(u,D)\mapsto(u+(D+20)/8,D/4-1)), when (u) is even and (D\equiv4\pmod8).

The forced first (F) from ((29-32c,55-64c)) leaves
[
u_0=16(c-1),\
D_0=32(c-1)+18=2u_0+18.
]

If a pair block has input (v), its output ((u_0,D_0)) satisfies one of two exact affine relations:

- after (EF), (v) is odd and (D_0=2u_0-2v+2);
- after (SF), (v) is even and (D_0=2u_0-2v-6).

These follow directly by substituting the definitions of (EF) and (SF).

## F-run identity

Suppose (m) consecutive (F)-blocks take ((u_0,D_0)) to ((u_m,D_m)). Then
[
u_m=u_0/2^m,qquad
D_m=D_0+6(u_0-u_m)+3m.
]
The second identity is the telescoping sum of the increments (3u+3) while (u) is successively halved.

Assume this F-run is immediately followed by a pair block. The endpoint is therefore either:

- (EF): (u_m) odd and (D_m\equiv0\pmod8);
- (SF): (u_m) even and (D_m\equiv4\pmod8).

Substituting the three possible starting relations gives the following residues. In each case (D_m\pmod8) is an expression of the form (C+3m), and the endpoint guard forces (m) into the displayed even residue classes.

| Starting point | Next block | Forced (m\pmod8) |
|---|---|---|
| Initial state (D_0=2u_0+18) | (EF) | (0,4) |
| Initial state (D_0=2u_0+18) | (SF) | (2,6) |
| After (EF), with (v) odd | (EF) | (2,6) |
| After (EF), with (v) odd | (SF) | (0,4) |
| After (SF), with (v) even | (EF) | (0,4) |
| After (SF), with (v) even | (SF) | (2,6) |

For clarity, the three congruence formulas are:

[
egin{aligned}
\text{initial: }D_m&\equiv -6u_m+2+3m\pmod8,\\
\text{after }EF: D_m&\equiv -2v-6u_m+2+3m\pmod8,\\
\text{after }SF: D_m&\equiv -2v-6u_m-6+3m\pmod8.
end{aligned}
]

The table follows by using odd residues (1,3,5,7\pmod8) for odd variables and even residues (0,2,4,6\pmod8) for even variables, then multiplying the forced congruence for (3m) by (3^{-1}=3\pmod8).

## Consequences

The F-run relation also gives the exact scaling identity
[
u_0=2^m u_m.
]
Thus the endpoint parity is a 2-adic valuation statement: if the next block is EF, (u_m) is odd and (v_2(u_0)=m); if the next block is SF, (u_m) is even and (v_2(u_0)\ge m+1). Combining this with the table yields:

| Starting point | Next block | Consequence for (v_2(u_0)) |
|---|---|---|
| Initial | EF | (v_2(u_0)\equiv0\pmod4) |
| Initial | SF | (v_2(u_0)\ge3) |
| After EF | EF | (v_2(u_0)\equiv2\pmod4) |
| After EF | SF | (v_2(u_0)\ge1) |
| After SF | EF | (v_2(u_0)\equiv0\pmod4) |
| After SF | SF | (v_2(u_0)\ge3) |

In particular, since the initial (u_0=16(c-1)), an initial run ending in EF requires (v_2(c-1)\equiv0\pmod4). This is a necessary condition for that branch, not a restriction on an initial SF branch.


1. **Every F-run followed by another pair block has even length.** This includes every F-run on a hypothetical infinite path, because Agent 22's theorem already establishes that such a path has infinitely many standalone (F)-blocks and paired blocks. Runs of length zero are included.

2. **The pair-type transition controls the run length modulo 4.** If the previous pair is (P\in\{E,S\}) and the next pair is (Q\in\{E,S\}), then
   [
   m\equiv
   \begin{cases}
   2\pmod4,&P=Q,\\
   0\pmod4,&P\ne Q.
   \end{cases}
   ]
   The initial state behaves as a virtual previous (S)-pair: initial-to-(EF) gives (m\equiv0\pmod4), while initial-to-(SF) gives (m\equiv2\pmod4).

This narrows the mixed-path problem to macro-words with even F-runs and a pair-type/run-length constraint. It does **not** by itself rule out an infinite mixed path. The next useful test is whether this restriction eliminates the mixed recurrent SCC in a refined weighted-state analysis, or yields a decreasing integer potential over complete macro-cycles.
