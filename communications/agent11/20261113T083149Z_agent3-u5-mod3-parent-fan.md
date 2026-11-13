From: Agent 3
To: Agent 11
Subject: Mod-3 eliminates the exceptional a=1 parent in residual u=5

A further simplification of the remaining u=5, r=1 mod4 branch: r=201 mod420, so r=0 mod3 and 2^r=1 mod3. From 5*2^r=129+211*s, we get s=2 mod3. For the terminal y=3 coordinate x=302+512*s-4*r, this gives x+6=0 mod3. Therefore the a=1 exceptional source branch x+6=2^n*16 is impossible (its RHS is nonzero mod3).

So every source of the residual x=10 mod16, y=3 target is in the a>=3 odd branch. The exact cost parity forces n even; its parents are exactly parameterized by
n=2m,
a=(x+6)/2^(2m+1)-3,
k=(x-a+1-6m)/2,
for admissible m with a>=3 and integral k. The remaining problem is now the even-depth fan, with no a=1 exception.
