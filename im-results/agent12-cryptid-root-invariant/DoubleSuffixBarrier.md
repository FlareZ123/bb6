# Triple-one halting barrier with arbitrary separated doubles

**Status:** original-source kernel accepted in [run 46041206114](https://github.com/FlareZ123/bb6/actions/runs/46041206114), source commit 8a01806ecfa6090d8331c42eca9f0be9f2edc938, job 140649099883, pinned Lean 4.35.0-rc4. The [Lean append](DoubleSuffixBarrier.append.lean) exports a12G_double_suffix_halts; the double exposures, token barrier, and G theorem all have only [propext, Classical.choice, Quot.sound]. The counted cost formula remains a source-clause paper derivation, supported by finite replay. No authentic root verdict or global Cover is claimed.

This restricted language is now subsumed by the [general triple-containing binary-word theorem](GeneralTripleBarrier.md), which removes the separation condition using a paired-token invariant. The simpler exact three-block recurrence below remains a useful independent source-proof slice.

## Theorem

Write G(M,U)=CR([0],0^M U), where M>=1 and U is a word of
first-coordinate pair values in {0,1}. If

    U = w 111 v,  w in (0|1)*,  v in (0|01|0011)*,

then G(M,U) halts. This strictly generalizes the earlier collectable-tail
language v in (0|01)*, and allows arbitrarily many double-one blocks.
For example, 11100110011 is newly covered. Here strings denote stack
entries, not binary integers.

## Unified token representation

The exact source definitions encode an ordinary right pair (a,b) as a+1
ones followed by one zero (b mod 1 = 0). Thus an ordinary CR state can be
represented by tok_CR(K,W,L), with K containing ordinary pair values plus
one, arbitrary remaining paired tape W, and L the first coordinates of
the opposite stack. Appending any finite zero-token padding on a blank
tail does not change the physical tape. This eliminates the need for a
separate case analysis of ordinary and token corridors.

Let High(K) mean K = (a+3)::T or K = 1::(a+3)::T, for a>=0 and arbitrary T.
Write d=0 or 1 respectively. Source pin:
google-deepmind/cryptids@3647718b5df22e1a61462dec0376bd204526285a,
BusyBeaver/BB6/Accelerations/M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.lean,
blob 7e1ac8acb4454a43d0354ea9a41be0cbda40a88c.

### Exact block rewrite and cost

The essential new identity is, for arbitrary c>=0, L, W, T, d in {0,1}:

    tok_CR(1^d [a+3] T,W,11[c]L)
      -> tok_CR(1^(d+4) [a] T,W,[c+1]L)

at 41+6d primitive transitions. Derivation:
tok_CR_1_1_cons_25 produces EL with left 00[c+2]L (25);
d tok_EL_1 transfers produce d more zeros (2d);
tok_EL_add3 initiates DR with token 2 (5);
d+2 tok_DR_zero transfers move the zero block (4(d+2));
tok_DR_succ decrements c+2 to c+1, prepending two ones (3).
All untouched tails remain arbitrary. These named source theorems occur
at lines 313–339 and 365–368 of the pinned file.

Consequently, while High(K) holds:

| CR-left block | Right token rewrite | Cost | New d |
| --- | --- | ---: | ---: |
| 0 | bump first token by 2 | 2 | 0 |
| 10 | replace first k by [1,k+3] | 5 | 1 |
| 1100 | replace 1^d [a+3] T by [1,4] 1^(d+3) [a] T | 46+6d | 1 |
| 111 (terminal) | expose left head 2, then tok_CR_add2_halts | 43+6d | — |

The first two rows are tok_CR_zero and tok_CR_1_0 (lines 349–359).
The third applies the new identity with c=0, then tok_CR_1_0 to the
remaining 10. The fourth uses c=1 and the two-step halt (lines 375–380).
Every nonterminal rewrite strictly consumes one entire block and preserves
High(K); induction on the number of blocks proves halting for arbitrary
P in (0|10|1100)* followed by 111 and any untouched left tail.

### G entry, scanning and exact time

Encode the G input as token sequence 1^M (U+1) [0,0] with W empty and left
[0]. tok_CR_zero then tok_CR_add2_nil_21 transfer into EL with left
[0,0,1] and the initial M tokens still pending (23 steps). Transfer the
M tokens (2M). Scan U via tok_EL_1 (cost 2 per zero) and tok_EL_2
(cost 7 per one), giving left 0 reverse(U) 0^(M+1) 1.
The two sentinel-zero tokens encode only blank padding. tok_EL_0_cons
followed by tok_CR_zero reaches CR with K=[3] and left
reverse(U) 0^(M+1) 1 at cost 3. Hence the initial High state has d=0,
and reverse(v) is exactly a concatenation of the permitted blocks.

For P=reverse(v), define C(P,d) by the table: C(empty,d)=43+6d;
C(0P,d)=2+C(P,0); C(10P,d)=5+C(P,1);
C(1100P,d)=46+6d+C(P,1).
The grammar is prefix-free, so the block decomposition is unique.
The exact total cost is

    2M + 26 + 2 #0(U) + 7 #1(U) + C(reverse(v),0).

This gives 240 primitive transitions at G(5,11100110011). It is an
explicit algebraic count of the source-clause trace, not a Lean
counted-reachability theorem (the existing ReachesPlus interface proves
only finite reachability).

## Executable evidence and formal acceptance boundary

The test [double_suffix_barrier.js](double_suffix_barrier.js) uses the
existing corrected source-transcription model without affine detection.
Actual V8 run: all 364 grammar block sequences of length at most 5;
8,736 ordinary CR cases, 6,552 token CR cases, and 4,368 G cases,
19,656 total. All halted at the exact formula time. Arbitrary sampled
tails and multiple high tokens exercise representation changes.
These finite tests are not the inductive proof.

The accepted append uses only the original source's named token clauses
and the earlier core sweep helper, not the old hazard1011
encoding. The source pin uses Lean 4.35.0-rc4. The current invocation's
local container and Python returned ClientError before even executing
the random draw; V8 and the GitHub connector work. The existing manual
workflow is extended with a separate double mode. The complete source build succeeded and all four new exported profiles were inspected.

## What this does and does not resolve

This is a strictly enlarged, exact-time prepared halting cylinder,
with a simpler uniform token representation than the previous
ordinary/token case split. Neither the original #85 blank seed nor
the #490 mirror blank seed is shown to enter it. A root-level proof
must establish the corresponding arithmetic return itinerary or a
sound invariant excluding all fatal cylinders. No BB(6) lower bound
or exact maximality result is asserted.
