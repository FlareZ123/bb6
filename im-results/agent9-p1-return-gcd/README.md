# Separated repeated-factor obstruction for P1

**Status:** standalone arithmetic theorem, locally kernel-checked Lean 4.36.0-rc2, no sorryAx. Original-source trace bridge still pending. Not an extinction or blank-machine verdict.

Let three occurrences of a length-L word x have signed clock offsets p,s from the first. Their right coordinates c,d,e follow the same recurrence at those shifted clocks. Set a_j=u(d_j-c_j)+v(e_j-c_j), with up+vs=g>0. Then 2a_{j+1}=a_j+g*x_j. For affine clock q±j and positive paired coordinates c,w bounded by C, write g=2^r h with h odd.

**New obstruction:** if -2^A<a_0<g+2^A, h(C+h)<2^B, and L≥A+r+2h+B, the three occurrences are impossible. In the coprime case the stronger unit-lock bound L≥A+B suffices, using the actual c_A,w_A<2^B, and even permits arbitrary base clock.

Proof: after A steps the auxiliary slope lies in [0,g]. Trim the final r positions, since r successor steps force the current slope divisible by 2^r. Scale to the odd slope h. Parity fixes the next slope and bit uniquely. Boundary slopes force a constant word (contradicting positivity by repeated halving). An interior slope has a primitive return of length p'<h, with p' distinct interior values, and forces p'-periodicity of the remaining word. Define b_j=±(c_{j+p'}-c_j) with the sign of the clock increment. The determinant H_j=h*b_j-p'*a'_j halves; its initial magnitude is less than 2^B, so integrality forces H=0. Thus the p' distinct slope values would give p' distinct integral b_j strictly between 0 and p', impossible.

This restriction concerns separated or overlapping occurrences; it does not assume consecutive repetition or an eventually periodic full word. It extends the existing periodic-word exclusions, rather than recomputing modular widths. It can apply after the delayed bits start, using the original positive two-coordinate micro recurrence.

Files (build in order with LEAN_PATH=. and lean -o NAME.olean NAME.lean):
- ReturnGCD.lean: common_word_slope, no_coprime_paired_returns, no_coprime_returns.
- ReturnSlope.lean: confinement, primitive return, parity determinism, finite halving.
- ReturnObstruction.lean: no_small_odd_slope.
- ReturnGeneral.lean: no_small_slope, no_small_gcd_returns.

All printed axioms are propext, Classical.choice, Quot.sound only.
