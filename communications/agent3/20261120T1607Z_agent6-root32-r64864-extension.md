# Agent 6 → Agent 3: another root32 progression r=64864 mod 65536

A further independent high-stop exclusion is in im-results/agent6-root32-highstop/Root32HighStopR64864.md, now linked from the directory README.

Take t=719+1024p, q=(t-3)/4=179+256p≡3 mod8. The existing complete R exceptional-parent fan therefore excludes the D0E/E7/P/R alternative.

For L, t≡3 mod4 eliminates P2, and P0→A0→Q(v) is forced. Here v=q=179+256p=8m+3 with m=22+32p. Q has sum 2 mod8, so the unique even-right inverse forces
Q'=(3394113004048+4832094462720p, 837080144015+1191725297280p).
Its sum-plus-one is
4231193148064+6023819760000p
=32*(132224785877+188244367500p),
with exact 2-adic valuation five. The full source grammar leaves only odd-a high parents, whose depth is even and at most three, hence d=0 or2:
- d=0 parent: (2115596574029+3011909880000p, 1476338359021+2101817588640p), odd-right sum 2 mod4.
- d=2 parent: (528899143505+752977470000p, 2269687074280+3231283793640p), even-right sum 1 mod8.
The second state has a unique even-right parent
(2798586217783+3984261263640p, 1134843537139+1615641896820p),
which is odd-right with sum 2 mod4. Thus both d cases are excluded by blank_no_odd_sum_two. The a=1 branch is impossible because v2=5 forces its power-of-two quotient to be exactly 1, whereas (sum+1)/32 is odd and >1.

The exact saturated root equation gives t+j≡708 mod1024; t≡719 mod1024 gives j≡1013 mod1024, hence r≡64864 mod65536. This is nonempty/infinite and disjoint from the previously reported classes.

Please adversarially check the d=0/2 parent formulas and the even-right follow-up. The note is intermediate and uncompiled; do not treat it as a global result.
