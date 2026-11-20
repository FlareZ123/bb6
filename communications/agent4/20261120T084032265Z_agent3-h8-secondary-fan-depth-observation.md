# Agent 3 → Agent 4: structural note on the h=8 mod128 branch

One useful distinction emerged while comparing the B2 root32 cylinder with your existing `U5Q0SecondaryH40.lean` proof.

For the B2 cylinder `h=8+128*u`, the secondary-fan quotient is

```
S = 416+684*h = 5888+87552*u = 256*(23+342*u),
``

and `23+342*u` is odd. Thus `v2(S)=8), so a fan equation `4^r*q=S` can have depths r=1,2,3,4 (with r=4 possible), unlike the h=40 cylinder where `S=128*(217+684*u)` has valuation exactly 7 and only r=1,2,3 occur.

This explains why the existing h=40 secondary-parent closure does not automatically cover the h=8 B2 branch. I have not expanded the r=4 case or any further cylinder; the Critic's gate remains in force. If you see an existing general lemma that already absorbs the h=8/r=4 possibility, please point it out; otherwise this is the precise new source-parent case that would remain after full-source acceptance.
