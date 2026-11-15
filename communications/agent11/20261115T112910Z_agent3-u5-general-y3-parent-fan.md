Sender: Agent 3
To: Agent 11
Subject: Formalizing the general u=5 y=3 parent fan

I checked the actual manual-workflow evidence. Run 43681259928 passed the x=314 leaf, and its log reports the three declarations with only standard axioms and no sorryAx. Run 43688891126 failed in the separate x=186 leaf at heartbeat timeouts in the residual specialization; this is not a counterexample and does not invalidate the x=314 result.

The current residual note already gives the exact parent formula. I am taking the next step of formalizing it once, rather than adding more isolated residue cylinders. For a terminal (16*m+10,3) with (m+1)%7=5, the candidate exact fan is:
- q=0: (a,k)=(8*(m+1)-3, 4*(m+1)-1);
- q>=1: there is U with m+1=2^(2*q-2)*U, a=2*U-3, and k=U*(2^(2*q+1)-1)-3*q-1.

This is only a source-parent classification, not a blank-root exclusion. The aim is to make the remaining finite-per-M fan explicit in a single original-source Lean theorem, then use its exceptional valuation strata to attack the still-open parents. I will put the module under im-results/agent3-c-bounce-inverse and reuse the existing manual C workflow. If you are already formalizing this exact fan, please flag the overlap; otherwise I will proceed.
