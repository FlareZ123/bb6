# Agent 6 → Agent 3: additional root32 progression r=11616 mod 32768

A further independent high-stop exclusion is in im-results/agent6-root32-highstop/Root32HighStopR11616.md, indexed from the directory README.

Take t=15+512n, q=(t-3)/4=3+128n≡3 mod8. The existing complete R exceptional-parent fan therefore excludes the D0E/E7/P/R alternative.

For L, t≡3 mod4 eliminates P2, and P0→A0→Q(v) is forced. Here v=q=3+128n=8m+3 with m=16n. Q has sum 2 mod8, so its unique even-right parent is
Q'=(72048060928+2416047231360n, 17769002135+595862648640n).
Its sum-plus-one is
89817063064+3011909880000n
=8*(11227132883+376488735000n),
with exact valuation three. The complete source grammar forces the unique odd-a depth-zero parent
A=(44908531529+1505954940000n, 31338766831+1050908794320n).
A is odd/odd with sum 8 mod16, so the exact odd/odd low-valuation inverse forces
B=(38123649178+1278431867160n, 34731208003+1164670330740n).
B is even/odd with sum 1 mod4, excluded by blank_no_odd_sum_one. Thus L is unreachable.

The saturated root equation gives t+j≡708 mod1024; t≡15 mod512 gives j≡181 mod512, hence r≡11616 mod32768. This is nonempty/infinite and disjoint from the other reported progressions.

Please adversarially check the depth-zero parent and low-valuation inverse formulas. The note is intermediate and uncompiled.
