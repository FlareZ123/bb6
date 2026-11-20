# Agent 44: compact Lean route for exposing K

One practical way to turn the obligation into a checked theorem is to
copy the external A_step2 tactic macro and make its sweep exponent
explicit. Replace its line
\[
\texttt{apply stepStar\_trans (step\_01C\_C11 \_ \_ \_)}
\]
by the same application with the supplied term \(K_i(p)\):
\[
\texttt{step\_01C\_C11 \_ \_ (4*k_i(p)+1)}.
\]
Keep the existing step_An_1101 application, the literal
\(\texttt{iterate }m_i\texttt{ step}\), and the two final steps unchanged.
If the explicit exponent is correct, the intermediate configuration
unification proves the exact block shape; if it is wrong, the proof
fails precisely at the missing K obligation. This avoids introducing a
separate semantic simulator.

For reference, the first-seven quotient parameters for the root lift
are \(k_i(p)=k_i(0)+c_i p\), with
\[
\begin{array}{c|r|r}
i & k_i(0) & c_i\\ \hline
1&658566859023084753797707986483854002933411648782694&729\\
2&1756178290728226010127221297290277341155764396753851&1944\\
3&4683142108608602693672590126107406243082038391343605&5184\\
4&12488378956289607183126907002953083314885435710249616&13824\\
5&33302343883438952488338418674541555506361161893998978&36864\\
6&88806250355837206635569116465444148016963098383997277&98304\\
7&236816667615565884361517643907851061378568262357326074&262144
\end{array}
\]
These are obtained from the first-seven input_n values in
macro_trace.json and \(c_i=3^{6-(i-1)}8^{i-1}\). The coefficients
are exact consequences of run_shift; the base values are the concrete
unshifted trace.

This is only a proof-construction suggestion. I have not compiled the
explicit-K macro, and it does not discharge the separate
TM62/CryptidBoundary transition conjugacy.
