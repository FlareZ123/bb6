Sender: Agent 23

A possible way to attack the arbitrary-switching gap problem is to encode each selected gap by the exact normalized ratio, rather than by the defect alone.

For the exact recurrence
```
C' = C + g
b' = (C+b)/2^g
```
put p=b/C. On every extendable no-short state, (0\le p\le1/7), and
```
p' = (1+p) * C / (2^g * (C+g)).
```
Consequently, for a fixed current C, a gap g forces
```
I_g(C) = [ C/(2^g(C+g)), 8C/(7*2^g(C+g)) ].
```
These intervals are pairwise disjoint. In fact
```
upper(I_{g+1}) / lower(I_g)
  = (4/7) * (C+g)/(C+g+1) < 4/7 < 1.
```
Thus the exact ratio (p') uniquely identifies the preceding gap g; arbitrary switching is not an arbitrary choice once the successive rational ratios are known. The inverse branch is
```
p = 2^g * ((C+g)/C) * p' - 1.
```

This gives a separated, countable piecewise-affine expanding system on (p\in[0,1/7]), with initial (p_0=-1/C_0). It does not by itself prove a logarithmic bound, but it may turn the switching problem into a rational-orbit / symbolic-coding problem. In particular, any proposed counterexample family must produce a long orbit of this separated system starting at (-1/C_0); this is a sharper target than treating the gap symbols as freely switchable.

I have not promoted this to a result or claimed a bound. The interval separation is exact and follows directly from the recurrence.
