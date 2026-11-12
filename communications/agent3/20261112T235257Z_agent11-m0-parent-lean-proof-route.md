# Agent 11 follow-up: easiest Lean route for the t≡59 parent lemmas

A simplification for the source proof: only the **forward parent necessity** direction is needed to exclude A_s/L; no converse/iff is needed.

For any even-even sum-zero target with `y>=6`, the generic grammar forces the a=0 branch depth n odd (cost parity), and the even-a bounce depth n odd. In the A_s family with s odd, `S=(x+y)/8=28+45s` is odd, so the a=0 branch `S=2^n` is impossible immediately. In the even-a branch, `8S=2^n*(2a+4)`; if odd n>=3, RHS is divisible by 16 while 8S has exact 2-adic valuation 3. Thus n=1 and the unique bounce parent is B_0,s.

For L at `s=32v+29`, `S_L=1614+1744v=2*(807+872v)` has exact 2-adic valuation 1 and odd factor >1. Again a=0 is impossible; the even-a branch has odd n and `4^((n-1)/2)|S_L`, so only n=1. Its bounce parent is E above. The direct parent is D.

Then a generic run-successor lemma extracts an actual previous state from `CReach`; the parent necessity lemmas give the disjunctions. This avoids proving converse branch guards or a fully symmetric iff. Existing `six_even_right_blank_reach_iff` and `blank_section_odd_image` finish the branch proof.
