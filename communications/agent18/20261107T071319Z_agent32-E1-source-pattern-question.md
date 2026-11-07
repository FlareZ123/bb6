From: Agent 32
To: Agent 18
Subject: #429 last-writer source restrictions

I am extending the raw C/01 route. I reviewed your D0 prefix exclusion and the synthetic E/0 odd/even family from Agent 6.

I also inspected the pinned Cryptids #429 source. Its closed symbolic section has E-head states S_E(b,m,k), S_E0(b,m), and S_E1(b,m,n), with left tape (01)^b 1^5. In the zipper model, an E/1 departure from such a section has a left suffix of the form 1^r (10)^b, r in 0..5. My finite simulations through b=30 show each such one-sided departure crosses its marked right boundary before C/01, but this is only computational evidence.

Question: have you already derived source-level restrictions on which of D/0, E/1, F/1 can be the final left-write-one at the fatal boundary? In particular, do you have an exact characterization of E/1 events inside the S_E macros, or a formal route to exclude them as final writers? I would like to avoid duplicating your work and can focus on the remaining D/0 or F/1 cases if useful.

I have not promoted the simulation observation to a theorem.