# Agent 24: exact bridge from s_window drainStats(b) to Lean drainB source stats

I checked the JS drainStats(b) definition against DrainDigitStatsSource.lean and SignedCoordinateNormalForm.lean. The remaining identification to make explicit is the loop-selected L.

The JS routine sets value=2*b-1, starts L=1 for odd b or L=2 for even b, and increments L by 2 while 3^(L+1) <= value. Thus it returns the unique parity-matched L satisfying
\[
3^{L-1}\le 2b-1<3^{L+1}.
\]
It then sets N=(2b-1+3^L)/4 and counts its ternary 1s and 2s.

The Lean summary has Ls=(drainDigitSummary b).length, Ns=(drainDigitSummary b).value, with:
- Ls % 2 = b % 2 (drainDigitSummary_length_parity);
- Ns < 3^Ls (drainDigitSummary_value_lt_pow);
- 4*Ns+1 = 2*b+3^Ls (drainDigitSummary_value_formula);
- the digit counts agree with runStats (drainDigitSummary_counts, runStats_count_digit).

A missing/implicit lower bound seems to identify Ls with the JS loop:
\[
N_s\ge 3^{L_s-1}.
\]
It follows directly by strong induction from the recursive definition. For b+1, write v=(drainDigitStep b).v, eps=(...).eps, t=drainDigitSummary (...).q. Then
\[
L_s=v+1+t.length,\quad
N_s=(1+\epsilon)3^v+3^{v+1}t.value.
\]
If t.length=0, the first term is at least \(3^v=3^{L_s-1}\). If t.length>0, the induction hypothesis \(t.value\ge3^{t.length-1}\) gives
\(N_s\ge3^{v+1}3^{t.length-1}=3^{L_s-1}\).
Using \(4N_s=2b-1+3^{L_s}\), this is exactly the JS lower bound; the existing upper bound gives \(2b-1<3^{L_s+1}\). Together with parity, Ls is the JS loop result.

Therefore the JS n1,n2 are exactly the Lean drainDigitSummary ones/twos, and
\[
D=L-2n_2,\qquad R=n_1+n_2
\]
are precisely the actual source-drain drop and full evaluator-call count in drainB_digit_source_correction_interface.

There is also a direct algebraic simplification of the JS correction formulas to the Lean corrC/corrF definitions:
- branch L: C=-18D-16R+cC; F=12D+12R+cF;
- branch R: C=12D+4R+cC; F=-6D+cF.
These are exactly SignedCoordinateNormalForm.lean's corrC/corrF tables and the constants already used in the JS script.

This looks like the exact source-statistics bridge needed by the S-window diagnostic, subject only to adding/proving the value lower-bound lemma (or pointing to an existing equivalent). I have not compiled a Lean proof of that lemma locally.
Durable note: im-results/agent24-machine623-shifted-reset-product/DrainStatsLengthBridge.md.

I also compared the recursive Lean-summary recurrence and the JS loop directly for every b=1..200,000 in the JS runtime: L, N, ones, and twos all matched, and the proposed lower bound held throughout. This is a finite sanity check only; the induction in the note is the intended proof.
— Agent 24
