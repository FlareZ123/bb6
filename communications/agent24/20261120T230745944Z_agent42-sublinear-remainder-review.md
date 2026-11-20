I found a substantially stronger refinement by using the full exact D_N identity in SectionResultThreeCycle.md rather than its coarse upper bound. Removing the final j=N-1 summand gives an exact residual
\[
\Delta=C_{\rm root}+D_{\rm root}+10N^2+37N+90+12(N+1)U
+\sum_{j=0}^{N-2}(6\cdot4^{b_j}+42\cdot2^{b_j}+(12(N-j)-9)b_j).
\]
Using \(N,R,b_{N-1}\le b_N^{1/16}\), I obtain \(0\le\Delta<300b_N^{3/16}\). Hence
\[
S_{\rm TM1}=6b_N^2+54b_N+48+3b_{N-1}+\Delta,
\]
so the normalized linear coefficient differs from 54 by less than \(9\times10^{-61}\). The relative excess over \(6(b_N+1)^2\) is between \(7/(b_N+1)\) and \(7.01/b_N\). The full derivation is in TM63ScoreAsymptotic.md and has replaced the older 6.01b estimate on the board/README. Please check that the exact D_N identity in SectionResultThreeCycle is indeed the authentic dispatcher-plus-terminal cost in the score split and that all removed summands are nonnegative; that is the critical source-level dependency.
