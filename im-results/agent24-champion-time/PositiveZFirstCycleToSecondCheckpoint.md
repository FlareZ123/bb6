# Positive-z first-cycle output is the second q4 checkpoint

**Status:** exact coordinate derivation from the current source definitions; not yet Lean-compiled. This is an intermediate source-proof target, not a halt theorem, a BB(6) lower bound, or evidence about later-cycle termination.

## Statement to formalize

Write
\[
a=2^z-1,\qquad H=3\cdot2^z+3z+7=3a+(3z+7)+3,
\]
and suppose
\[
z\ge1,\qquad q<2^w,\qquad q\equiv1\pmod2.
\]
Put \(r=(q-1)/2\). Then \(w\ge1\), \(r<2^{w-1}\), and the source encoder identity is
\[
\operatorname{binDec}(w,q)=d_0\mathbin{++}\operatorname{binDec}(w-1,r).
\]

The existing first-cycle composition positiveZFirstCycle_from_checkpoint ends in state 4 at head 1. Its exact output tape should be the q4-side encoding
\[
q4TapeFromSides(L_2,R_2,1),
\]
where
\[
L_2=[0,1,1]\mathbin{++}d_1\mathbin{++}d_0
       \mathbin{++}\operatorname{binDec}(w-1,r)\mathbin{++}lh
\]
and
\[
R_2=[0,0,0]\mathbin{++}1^H\mathbin{++}[0,0]
       \mathbin{++}d_1^{\,2^a}.
\]
Here \(d_0=[0,0,1]\), \(d_1=[1,1,1]\), and \(d_1^{2^a}\) means d1pow (2^a). In particular the output satisfies the exact input contract of secondCyclePrefix_from_checkpoint with
\[
m=H,\qquad n=2^a=2^{2^z-1},\qquad h=1.
\]
This makes the first-cycle endpoint the second q4 checkpoint (counter value changes from \(q\) to \(2q\), with width from \(w\) to \(w+1\)).

## Why the tape identity has these coordinates

The first-cycle endpoint module identifies the pre-drain state as
\[
S_0(\ell,a,2^a-1,0,H),
\quad
\ell=1^{3z+7}\mathbin{++}[0,1,0,0]
       \mathbin{++}1^4\mathbin{++}\operatorname{binDec}(w,q)
       \mathbin{++}lh.
\]
After s0Config_counted_drain_closed, the drained state is
\[
S_0(\ell,a,0,2^a-1,H).
\]
The exact S0 encodings give
\[
s0LeftFacing(\ell,a,0)=d_1^{a}\mathbin{++}\ell,
\qquad
s0RightFacing(2^a-1)=[0,1,1,1,0,0]\mathbin{++}d_1^{2^a}.
\]

The Q postlude then applies sweptLeft for
\[
k=3a+(3z+7)=H-3
\]
cells, from head \(H\) to head 3, followed by the four-step firstCyclePostlude_at bridge, which ends in state 4 at head 1 and writes the local cells 0..3 as \([1,0,0,0]\).

For the counted sweep, the exact tape profile is:
- cells \(x\le3\) are unchanged;
- cell 4 is zero;
- cells \(5\le x\le H+1\) are one;
- cells \(x>H+1\) are unchanged.

The postlude frame overwrites cells 0..3 as \([1,0,0,0]\). Thus the new right-facing stream from head 1 is:
- cells 2,3,4: 000;
- cells 5 through \(H+4\): all one (the sweep contributes 5..H+1 and the original S0 right side contributes H+2..H+4);
- cells H+5,H+6: 00;
- cells H+7 onward: d1pow (2^a), then blank.

This is exactly \(R_2\).

For the left-facing stream from head 1:
- cells 1,0 are the postlude-written 0,1;
- cells -1,-2,-3,-4 are the four trailing ones in \(\ell\);
- cells -5,-6,-7 are the first d0 block of binDec(w,q), because q is odd;
- the remaining tail is binDec (w-1) r ++ lh.

Consequently the stream is
\[
[0,1]\mathbin{++}1^4\mathbin{++}\operatorname{binDec}(w,q)\mathbin{++}lh
=[0,1,1]\mathbin{++}d_1\mathbin{++}d_0
 \mathbin{++}\operatorname{binDec}(w-1,r)\mathbin{++}lh,
\]
which is \(L_2\).

## Lean proof obligations

1. Prove the generic counted-sweep profile for sweptLeft n T h, under leftOnes T h n and T (h+1)=false:
   - unchanged for x < h-n+1;
   - zero at x=h-n+1;
   - one for h-n+2 ≤ x ≤ h+1;
   - unchanged for x>h+1.
   The first property already appears privately as sweptLeft_preserves_left in PositiveZFirstCycleBridges.lean; the other three are short inductions on n.
2. Use firstCycleS0DrainOutput_leftOnes, firstCycleS0DrainOutput_rightZero, and the S0 side-cell lemmas to establish the left/right profile above.
3. Rewrite binDec w q with binDec_odd (w-1) ((q-1)/2).
4. Prove the final Config equality by state/head/tape extensionality.
5. Apply secondCyclePrefix_from_checkpoint with m=H, n=2^a, h=1; its hinput34, hfirst, separators, d1-blocks, and five trailing zeros follow directly from \(L_2,R_2\).

The existing second-cycle prefix cost is
\[
34+H+2+3\cdot2^a+29
=3\cdot2^{2^z-1}+3\cdot2^z+3z+72.
\]
Composing this after the first cycle would extend the exact source run through the second q4-tail frame. It still would not establish halting or the complete later-cycle recurrence.
