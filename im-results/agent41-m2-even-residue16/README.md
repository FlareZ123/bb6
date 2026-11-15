# m=2, n=32k+16 source row

## Mathematical target

This closes the next currently relevant even-marker reset class:

\[
(m,n)=(2,32k+16),\qquad k\ge 0,
\]

so \(v_2(n)=4\). The source transition is

\[
S_1(L,32k+16,2,a,0,b,h)
\longrightarrow^*
S_1(L,32k+15,1,a+b+2,0,2^b-1,h+5+3b).
\]

The exact increment cost is

\[
6\cdot4^b+42\cdot2^b+71+12a-9b.
\]

The proof is split into a finite base case n=16, a five-BinDec-block frame lift, the generic q4 suffix, and the existing counted drain.

## Finite n=16 q4 bridge

After the standard left sweep of 3a+2 one-blocks, the finite bridge starts in state 3 at local head 0 with marked cells

\[
\{-16,-15,-14,-13,-12,-11,-10,-9,-8,-7,-6,-5,-4,-1\}.
\]

The exact 74-step bridge ends in state 4 at local head 2 with marked cells

\[
\{-18,-17,-16,-13,-10,-7,-4,-1,1\}.
\]

Every intermediate bridge head is in [-18,1]. The kernel is recorded as an exact fRun tm2 74 theorem by decide in M2EvenSixteenQ4Prefix.lean.

For the base n=16 prefix:
- left sweep: 3(3a+2)=9a+6 steps;
- finite bridge: 74 steps;
- right E-scan: 3a steps;
- total q4 prefix: 80+12a steps.

The generic q4 suffix costs 39+3b, giving reset-prefix cost 119+12a+3b. The counted drain then contributes

\[
6\cdot4^b+42\cdot2^b-12b-48,
\]

yielding the increment formula above.

## Lift to all n=32k+16

The low five BinDec blocks are stable:

\[
\operatorname{binDec}(L,32k+16)
 = d_1^4\,d_0\,\operatorname{binDec}(L-5,k),
\]
\[
\operatorname{binDec}(L,32k+15)
 = d_0^4\,d_1\,\operatorname{binDec}(L-5,k).
\]

The source and q4 target therefore share a 3a+22-cell left prefix. The frame includes that entire prefix; the base-run head bound is stronger than the chosen frame boundary. The high-order quotient tail is preserved unchanged.

The formal source files are:
- M2EvenSixteenQ4Prefix.lean: finite bridge, base q4 prefix, and head bound;
- M2EvenResidueSixteen.lean: frame lift, reset prefix, and counted increment.

## Root application

At the middle-15 endpoint, the current root arithmetic gives n=16r, where r is odd. Put k=r/2; then 16r=32k+16. TM63RootResidueZero.lean composes this row and defines a candidate exact original-machine prefix through middle row 16. The resulting m=1, n=32k+15 state is then handled by the distinct n=8q+7 row in ../agent41-m1-odd-residue7/M1OddResidueSeven.lean; TM63RootResidueSeven.lean extends the candidate root prefix through middle row 17.

This does not solve BB(6), prove the machine halts, or establish an upper bound. The new Lean files remain candidate source proofs until they compile against the original transition table and pass transitive axiom audits.

## Experimental scope

The deterministic replay script checks the exact 74-step bridge and the q4 cut, suffix intermediate, and counted-drain endpoint for 24 cases: k=0..3, a in {1,2}, b in {0,1,2}. This is computational corroboration only; the finite bridge's intended proof object is the Lean decide theorem, and the generic row relies on the frame and counted-drain proofs.
