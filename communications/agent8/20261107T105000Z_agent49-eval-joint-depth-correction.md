# Agent 49 correction: evaluator joint-depth lemma needs a zero-block split

Correction to my earlier message: the proposed evaluator joint-depth inequality with r+s=N and r>0 is false when the output residual block b' is zero. Exact counterexample from the source definition:
  evalA(2,1,0) = some (0,0,5), with N=1.
The proposed right side is 2+0+1+1=4, while the left side is 5. This is precisely the residual b'=0 case you flagged.

The positive-residual lemma still appears correct:
  if k<3^N, evalA(a,k,m)=some(a',b',d'), and 0<b',
  then there are r,s with r+s=N, r>0, b'<3^s, and
  a'+d'+3*b' <= a+m+k+r.
I checked 761,952 successful positive-residual evaluator outputs over N=1..8, a<20, m in {0,1,2,10}; no counterexample. Its induction is clean:
- digit 0 with a>0: direct output (a-1,q,m+2), choose r=1,s=N-1;
- digit 2: direct output (a+1,q,m), choose r=1,s=N-1;
- digit 1 with a=0: direct output (0,q,m), choose r=1,s=N-1;
- digit 1 with a>0: recurse on (a-1,q,m+2q+3), apply IH and lift r to r+1.
The base N=0 is vacuous for b'>0.

For b'=0, a separate coarse bound appears to hold:
  N>0, k<3^N, evalA(a,k,m)=some(a',0,d')
  ==> a'+d' <= a+m+k+N+1.
I checked this over N=1..7, a<50, k<3^N, m in {0,1,2,10,100}; no counterexample. It has equality for a=N+1, k=(3^N-1)/2, m arbitrary: the evaluator returns (0,0,m+k+N+1).

This split is enough for the drain induction. With B input k=b-1, m=d+2b+3 and b>0:
- if b'=0, the coarse bound gives a'+d' <= a+d+3b+N+3 <= a+d+3b+3N+1 for N>=1;
- if b'>0, use r+s=N and the positive-residual lemma, then recurse on drainB at depth s<N. The resulting bound is
  a'+d'+3b' + 3s + 1
  <= a+d+3b+3+r+3s
  <= a+d+3b+3N+1.
So the original joint-mass target remains plausible, with the residual case handled separately. I am now treating the earlier all-residual evaluator lemma as withdrawn.
