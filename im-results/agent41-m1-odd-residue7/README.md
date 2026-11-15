# m=1, n=8q+7 source row

## Mathematical target

The next root successor after the m=2, n=32k+16 row has marker 1 and
n=32k+15=8(4k+1)+7. The source theorem is generalized to every q≥0:

\[
S_1(L,8q+7,1,a,0,b,h)
\longrightarrow^*
S_1(L,8q+6,0,a+b+2,0,2^b-1,h+5+3b).
\]

The exact increment cost is

\[
6\cdot4^b+42\cdot2^b+19+12a-9b.
\]

## Finite bridge and prefix

The left sweep has N=3a+1 one-blocks and costs 3N=9a+3. It exposes the same
26-step finite bridge already formalized in M1OddQ4Bridge:

- start: state 3, local head 0, marked cells {-4,-1};
- end: state 4, local head 2, marked cells {1,-1,-4,-5,-6};
- every bridge head is in [-6,1].

The following right E-scan has length 3a-1 and returns the head to h. Thus
the q4 prefix costs

\[
3(3a+1)+26+(3a-1)=28+12a.
\]

The q4 suffix costs 39+3b, so the reset prefix costs 67+12a+3b. The existing
counted drain costs 6*4^b+42*2^b-12b-48.

## Three-block BinDec lift

The stable low-order words are

\[
\operatorname{binDec}(L,8q+7)
 = d_0^3\,\operatorname{binDec}(L-3,q),
\]
\[
\operatorname{binDec}(L,8q+6)
 = d_1\,d_0^2\,\operatorname{binDec}(L-3,q).
\]

The source and q4 target left-facing streams share a 3a+8-cell prefix
boundary and the common tail begins at index 3a+8. The bridge's [-6,1]
window supplies the required boundary pattern. The generic q4 suffix and
counted drain then produce the exact source transition.

Formal source: M1OddResidueSeven.lean. The deterministic replay script checks
the finite bridge and 24 cases q=0..3, a in {1,2}, b in {0,1,2}.

## Root use and proof status

For the root branch after middle16, q=4k+1, so this row applies directly and
would extend the candidate blank-root prefix through middle17. This is not
a proof that the machine halts or an upper bound for BB(6). The new Lean
source module is not yet locally compiled or CI-verified; treat it as a
candidate proof until the targeted source audit is complete.
