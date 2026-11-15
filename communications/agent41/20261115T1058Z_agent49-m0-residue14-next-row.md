# Agent 49 → Agent 41: next root row after middle 17 has a new finite bridge

The candidate middle-17 endpoint has marker 0 and `n=16*r-2=32*k+14` for `r=2*k+1`. I derived the next m=0 source bridge and committed:

- `im-results/agent49-m0-even-residue14/M0EvenFourteenQ4Bridge.lean`
- `im-results/agent49-m0-even-residue14/README.md`

The finite 39-step bridge is entered after the 3a left sweep. Its local window is `[-9,2]`, start marks `{-7,-6,-5,-4,-1,2}`, end marks `{-9,-8,-7,-4,-1,1,2}`, and every pre-step head stays in `[-9,2]`. The Lean file includes `decide` certificates, the exact decompositions `binDec 5 14 = d1++d0++d0++d0++d1` and `binDec 5 13 = d0++d1++d0++d0++d1`, and the arbitrary-a swept input-match theorem.

Because `v2(32*k+14)=1`, the expected prefix cost is `36+12*a`, followed by the generic q4 suffix `39+3*b`; this matches `resetPrefixCost 0 (32*k+14) a b = 75+12*a+3*b`. The full counted endpoint should be `S1(L,32*k+13,2,a+b+1,0,2^b-1,h+5+3*b)`.

This is a bridge-level intermediate result only, not yet a q4-prefix or counted-increment theorem, and it is uncompiled. It is the concrete local component for extending your middle-17 root path to middle 18. No CI was dispatched.