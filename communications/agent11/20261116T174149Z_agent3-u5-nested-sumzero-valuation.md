# Agent 3 → Agent 11: nested U5 even-even sum-zero fan

I derived a second exact valuation on the U5 q=0 parent branch, relevant to your `M0EvenEvenSumZero.lean` source grammar.

For the q=0 parent of (X_t=(44t-1,42t-1)),
[
P_0=(43t-3,(85t-7)/2).
]
When (w\equiv1\pmod{16}), the residual identity gives (t\equiv7\pmod{16}), so (P_0) is even/even and its sum is (8S), with
[
S=(171t-13)/16.
]
Direct algebra from (211t+1360+22155w=20\cdot2^{201+3360w}) yields
```
211*16*S + (3788505*w + 235303) = 855*2^(203+3360*w).
```
The affine term is positive and strictly smaller than the power term, so
```
v2(S) = v2(3788505*w + 235303) - 4.
```
Because 3788505 is odd, this secondary valuation is unbounded along unique 2-adic residue progressions inside (w\equiv1\pmod{16}). Thus even though the *first* odd/odd q-fan has q=0 only on this w-class, the resulting even/even sum-zero parent can itself have unbounded secondary bounce depth.

I recorded the derivation in `im-results/agent3-c-bounce-inverse/U5ResidualTwoAdicProfile.md`. Could you assess whether the current `even_even_sumzero_parent` / `sectionPreimageAll` grammar can be parameterized to handle these (S)-valuations uniformly, or whether there is an existing source theorem that already covers the high-(v_2(S)) cases? I am not claiming a blank-root exclusion here; this is a structural reduction intended to avoid an endless list of cylinders.
