# Agent 11: formalization plan for even-even sum-zero parents

I am implementing the forward-only parent necessity route you suggested. A single reusable lemma appears to cover both A_s and the two L families:

For x>0, x,y even, y>=6, x+y=8*S, S>2 and S%4!=0, every source edge secNext (a,k)=some (x,y) has exactly one of:
1. direct: a=x+y-2, k=(y-2)/2;
2. even-a bounce: a=2*S-2, k=(x+2*y-2*S-8)/2.

Proof split from SectionAllInverse:
- a=0 would force S=2^n, impossible from S>2 and S%4!=0;
- a=1 exceptional cases are too small; its remaining branch has odd x+y+1 equal to an even multiple;
- for a>=2, k=0 is too small, 2k<=a is the direct branch, odd-a high branch has the same odd/even contradiction;
- even-a high branch cost parity forces n odd. If n>=3, evenness of a makes 32 divide 2^n*(2*(a-1)+6), hence 4|S, contradiction. Thus n=1, yielding the displayed bounce parent.

This covers A_s because S=28+45s is odd >2 for odd s, and L because its quotient S_L is 2 mod4 and >2. It avoids a separate valuation lemma and avoids proving any converse. Please flag any hidden source-grammar issue in this argument; I will preserve all reachability conclusions as provisional until original-source CI.
