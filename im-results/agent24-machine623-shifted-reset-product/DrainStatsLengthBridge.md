# Drain-statistics length bridge for the S-window diagnostic

**Status:** exact algebraic bridge with one small Lean lemma identified; proof sketch not yet compiled. This is an intermediate result, not an academic result.

## JS and Lean conventions

In Agent 48's s_window_boundary_phases.js, drainStats(b) sets
\[
v=2b-1,
\]
starts \(L=1\) when \(b\) is odd and \(L=2\) when \(b\) is even, and increments \(L\) by two while \(3^{L+1}\le v\). It then computes
\[
N=(v+3^L)/4
\]
and counts the ternary digits \(n_1,n_2\) of \(N\).

The Lean file DrainDigitStatsSource.lean defines
\[
L_s=(\texttt{drainDigitSummary }b).\texttt{length},\qquad
N_s=(\texttt{drainDigitSummary }b).\texttt{value}.
\]
Existing theorems give:
- \(L_s\equiv b\pmod 2\);
- \(N_s<3^{L_s}\);
- \(4N_s+1=2b+3^{L_s}\), equivalently \(4N_s=2b-1+3^{L_s}\);
- the summary's one/two digit counts agree with runStats via drainDigitSummary_counts and runStats_count_digit.

The missing identification between the JS loop and \(L_s\) is the lower bound
\[
N_s\ge3^{L_s-1}\qquad(b>0).
\]

## Proof sketch for the lower bound

Use strong induction on \(b\). For \(b+1\), let
\[
v=(\texttt{drainDigitStep }b).v,\quad
\epsilon=(\texttt{drainDigitStep }b).\epsilon,\quad
t=\texttt{drainDigitSummary }((\texttt{drainDigitStep }b).q).
\]
The recursive definition gives
\[
L_s=v+1+t.\texttt{length},
\]
\[
N_s=(1+\epsilon)3^v+3^{v+1}t.\texttt{value}.
\]
If \(t.\texttt{length}=0\), then \(N_s\ge3^v=3^{L_s-1}\), since \(\epsilon\ge0\) and the second term is nonnegative.

If \(t.\texttt{length}>0\), the induction hypothesis gives
\[
t.\texttt{value}\ge3^{t.\texttt{length}-1}.
\]
Consequently
\[
N_s\ge3^{v+1}3^{t.\texttt{length}-1}
=3^{v+t.\texttt{length}}
=3^{L_s-1}.
\]

Combining this with \(4N_s=2b-1+3^{L_s}\) gives
\[
3^{L_s-1}\le2b-1<3^{L_s+1}.
\]
Together with \(L_s\equiv b\pmod2\), these are exactly the bounds defining the JS loop's unique parity-matched \(L\). Therefore the loop returns \(L=L_s\), and its \(N\) equals \(N_s\).

The JS digit counts \(n_1,n_2\) are consequently exactly the Lean summary counts. The source theorem drainB_digit_source_correction_interface then identifies
\[
D=L-2n_2=a-aa,\qquad R=n_1+n_2
\]
with the actual drainB first-counter drop and complete evaluator-call count.

## Independent finite check

I independently implemented the recursive DrainDigitSummary recurrence and the JS loop in the available JS runtime for every \(b=1,\ldots,200{,}000\). There were zero mismatches in \(L\), \(N\), the number of ternary 1s, or the number of ternary 2s; the proposed lower bound \(N_s\ge3^{L_s-1}\) held in every case. This is supporting computation only; the induction above is the intended universal proof.

## Correction formulas reduce exactly to the Lean cocycle

The JS script writes the corrections using \(L,n_1,n_2\). Substituting \(D=L-2n_2\) and \(R=n_1+n_2\) gives:

- Branch L:
  \[
  C=-18D-16R+c_C,\qquad F=12D+12R+c_F.
  \]
- Branch R:
  \[
  C=12D+4R+c_C,\qquad F=-6D+c_F.
  \]

These are exactly the corrC and corrF definitions in SignedCoordinateNormalForm.lean, with the same sector/branch constants. For example,
\[
-18D-16R=-18L-16n_1+20n_2,
\]
\[
12D+12R=12L+12n_1-12n_2.
\]
The right-branch identities are equally direct.

## Consequence and remaining action

Once the lower-bound lemma is formalized, the S-window diagnostic's drainStats(b), D, R, C, and F are connected to the Lean source-level drainB interface, rather than being an independent arithmetic model. The remaining work is to add and compile the small lower-bound lemma (or identify an existing equivalent) and then check the source-to-target digit transducer's interval conventions against the same Lean root transition.

No Lean proof was compiled during this invocation.
