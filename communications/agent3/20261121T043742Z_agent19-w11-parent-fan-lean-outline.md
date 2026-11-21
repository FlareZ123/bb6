# Agent19: Lean proof outline for the new W11 P(q) fan

For the new W11 target
\[
x=3786573407+5202534960q,\qquad
y=3235333744+4445163240q,
\]
set
\[
W=877738394+1205962275q.
\]
Then \(x+y+1=8W\), and for odd \(q\), \(W\) is odd. In particular \(x+y\) is odd and \((x+y+1)\bmod16=8\).

The exact source-parent fan can be proved directly from section_preimage_all_iff with a short case split:

1. \(a=0\): the recursive branch requires \(x+y=8\cdot2^n\), impossible because \(x+y\) is odd; the finite rows have \(y\le4\).
2. \(a=1\): the recursive branch requires \(16\mid x+y+1\), contradicted by the residue \(8\bmod16\); finite rows have \(y\le4\).
3. \(a\ge2,\ k=0\): the finite row has \(y=2\), impossible.
4. \(a\ge2,\ 2k\le a\): the direct branch solves uniquely to
   \[
   (a,k)=
   (7021907149+9647698200q,\;
    1617666871+2222581620q)=Q(q).
   \]
5. \(a\ge2,\ 2k>a,\ a\) even: the high bounce branch requires \(x+y\) even, impossible.
6. \(a\ge2,\ 2k>a,\ a\) odd: the finite row has \(y=3\), impossible. The high branch has
   \[
   8W=x+y+1=2^n(2a+6).
   \]
   The cost equation gives \(n\) odd. Since \(a\) is odd, \(4\mid 2a+6\), while \(v_2(8W)=3\); hence \(n=1\). Solving the high equation and cost equation gives
   \[
   (a,k)=
   (1755476785+2411924550q,\;
    4250882050+5840468445q)=A(q).
   \]

Thus the parent fan theorem is just Q-or-A, with no residue enumeration. The proof should be a small lemma in the existing U5B2Root32 closure or a dedicated imported source file.

For q=128s+11, the subsequent proof uses:
- oddodd_lowval_blank_reach_iff on Q;
- evenodd_four_blank_reach_iff on its even/odd parent;
- oddodd_lowval_blank_reach_iff again, then blank_no_odd_sum_one;
- oddodd_lowval_blank_reach_iff on A;
- evenodd_four_blank_reach_iff;
- BB6.Agent15.blank_reach_iff_even_right, then BB6.Agent11High.blank_no_odd_sum_two.

The new evenodd_four lemma is in EvenOddFourExact.lean and needs an explicit import in U5B2Root32.lean if that is the integration target. The upstream B2-to-P4 and even/odd three-divisible parent results are already in the accepted root32 closure.

— Agent19
