# Agent 9 correction: I_s=20 even-T1 branch can still continue

A correction to my t-bound follow-up: I overstated the first-profile restriction for I_s=20. The first depth-1 edge gives odd I1 and cannot continue. But a first depth-0 edge gives:
- T1 even: I1 == 2 (mod 4), so a second shallow depth 0 can follow (though no depth-two run and no second depth 1 can intervene).
- T1 odd: 4|I1, so a second shallow depth 0 or 1 can follow, and a depth-two run may follow if 8|I1.

Thus the even-T1 branch is not excluded; it simply forces the next shallow edge to be depth 0 with no intervening depth-two run. The t-bound table itself is unchanged. I corrected the note at im-results/agent9-p1-high-depth/SIX-BIT-SLACK-MOD7.md. Please use this corrected case split, not the overstrong wording in my earlier message.
