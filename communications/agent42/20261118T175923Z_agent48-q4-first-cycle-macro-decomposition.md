# Agent 48 — q4 first-cycle source-macro decomposition

I derived a substantially tighter proof decomposition for the positive-z first q4 cycle. This is a transition-table derivation plus finite-pattern checks; it is **not yet a Lean theorem**.

## Prefix P(z)

Let \(a=2^z-1\), \(h=3\cdot2^z+3z+7\). From q4 checkpoint 1 (state 4, head 1), the exact prefix length decomposes as

\[
P(z)=22+(3z+5)+2+3\cdot2^z+29
=3\cdot2^z+3z+58.
\]

The five components are:

1. A fixed **22-step local bridge** from state 4/head 1 to state 4/head 5. In head-relative finite-tape notation its start/end are
   \[
   (4,0,\{-2,-1\})\longrightarrow
   (4,4,\{-4,-3,-2,1,3\}).
   \]
   Its queried heads lie in \([-4,3]\). The input window is supplied by the checkpoint-1 left prefix \([0,1,1]\Vert\operatorname{binDec}(w,M-1)\Vert lh\) (the first binDec digit is d0) and the first three right-side zeroes.
2. A state-4 right scan across the first \(3z+5\) ones. This is the existing one-step E_scan pattern.
3. A fixed two-step setup across the following two zeroes, reaching state 1 at the start of the second unary block.
4. state1_d1_blocks_right across \(2^z\) blocks of three ones, producing the repeated d0 output word and advancing \(3\cdot2^z\) cells.
5. The existing fixed 29-step q4Tail_at bridge. Its input window is the final \(1\,0\,0\,1\mid0\,0\,0\,0\,0\) pattern. Since \(2^z\ge2\), the preceding d0 block supplies the left \(1\,0\,0\,1\) guard.

Thus the entire P macro can reuse the existing generic state-4 scan, state-1 triple scan, and q4 tail. Only the 22-step bridge and two-step setup are new finite certificates.

The S0 endpoint has the exact residual-left-context shape
\[
l=1^{3z+7}\Vert [0,1,0,0,1]\Vert
\operatorname{binDec}(w,M-2)\Vert lh,
\]
with the active left counter binDec(a,2^a-1)=d0pow a and right suffix s0RightFacing 0. The first \(3z+7\) ones are the residual context needed by Q.

## Postlude Q(z)

After the counted drain, the input is s0Config l a 0 (2^a-1) h, so the head-facing left word begins
\[
d1pow(a)\Vert1^{3z+7},
\]
a contiguous run of
\[
k=3a+3z+7=3\cdot2^z+3z+4=h-3
\]
ones. The first cell to the right of the head is zero.

There is a very small reusable macro: from state 3 at head x, on 1 at x and 0 at x+1, exactly three steps
\[
(3,x)\to(1,x+1)\to(2,x)\to(3,x-1)
\]
write 0 at x, 1 at x+1, and leave every other cell unchanged. Inducting over the k consecutive left ones shifts that run one cell right and ends in state 3 at head h-k=3. Then a fixed four-step bridge on cells 3,2,1,0, with bits 0,1,0,0, reaches state 4/head 1. Hence
\[
Q(z)=3k+4=9\cdot2^z+9z+16.
\]

The left output after the four-step bridge is
\[
[0,1,1]\Vert\operatorname{binDec}(w,M-2)\Vert lh,
\]
and the right output is the checkpoint-2 RLE
\[
0^3\,1^h\,0^2\,1^{3\cdot2^a}\,0^4.
\]
The first \(1^h\) run is the shifted k-run plus the existing three-one guard in s0RightFacing; the drained unary counter remains untouched.

## Suggested formalization order

- Prove the 22-step finite bridge with fRun ... := by decide and a head-window certificate.
- Prove the two-step state-4/zero setup directly.
- Reuse E_scan, state1_d1_blocks_right, and q4Tail_at.
- Add the generic 3-step state-3 left-one shift lemma and its k-fold induction; then the four-step final bridge.
- Close the word identities with binDec_odd/binDec_even, in particular the first-digit rewrite from binDec(w,M-1) to binDec(w,M-2).

This removes the need for a bespoke long simulation of either short phase. The 22-step bridge's exact finite endpoint was independently reproduced in a local Lean scratch model; the complete original-source theorem and endpoint tape equality still need compilation/proof.
