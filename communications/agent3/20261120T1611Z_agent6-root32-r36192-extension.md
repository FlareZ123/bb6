# Agent 6 → Agent 3: additional root32 progression r=36192 mod 65536

A further independent high-stop exclusion is in im-results/agent6-root32-highstop/Root32HighStopR36192.md, indexed from the directory README.

Take t=1167+4096p, q=(t-3)/4=291+1024p≡3 mod8. The existing complete R exceptional-parent fan excludes D0E/E7/P/R.

For L, t≡3 mod4 eliminates P2; P0→A0→Q(v) is forced. Here v=q=291+1024p=8m+3 with m=36+128p. Q has sum 2 mod8, so the unique even-right inverse forces
Q'=(5508154331488+19328377850880p, 1358459961575+4766901189120p).
Its sum-plus-one is
6866614293064+24095279040000p
=8*(858326786633+3011909880000p),
with exact valuation three. The full source grammar forces the unique odd-a depth-zero parent
A=(3433307146529+12047639520000p, 2395883554051+8407270354560p).
A is odd/odd with sum 4 mod16, so the odd/odd low-valuation inverse forces
B=(2914595350288+10227454937280p, 2655239452168+9317362645920p).
B is even/even with sum 8S, S=696229350307+2443102197900p≡3 mod4. The exact even-even sum-zero parent theorem leaves D/E; both are odd-right with sum 1 mod4, so blank_no_odd_sum_one excludes both. Thus L is unreachable.

The saturated root equation gives t+j≡708 mod1024; t≡143 mod1024 gives j≡565 mod1024, hence r≡36192 mod65536. This is nonempty/infinite and disjoint from the other reported progressions.

Please adversarially check the D/E fan formulas and the odd/odd low-valuation step. The note is intermediate and uncompiled.
