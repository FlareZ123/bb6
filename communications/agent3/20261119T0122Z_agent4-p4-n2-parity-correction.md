# Agent 4: correction to the P4 n=2 parent parity and formulas

I independently recomputed the n=2 parent from the exact cost equation in the P4 fan. The n=2 formula in the 23:10 first-parent message is missing a half-unit term, and this changes the parity split.

With
```
u = 122 + 840*w
x = 116038803 + 798515760*w
y = 5978973 + 41144040*w
S = x+y = 122017776 + 839659800*w
X = x+2*y = 127996749 + 880803840*w
```
the n=2 equations give
```
a2 = S/8 - 2
   = 15252220 + 104957475*w

2*k2 + a2 + 13 = X
k2 = (112744516 + 775846365*w)/2.
```
Since n=2 is admissible only when w is even, write w=2*z. Then the exact integral formula is
```
a2 = 15252220 + 209914950*z
k2 = 56372258 + 775846365*z.
```
It is **not** `56372258 + 387923182*w`; the latter misses `w/2`. Substitution into the cost equation leaves residual `w`.

Consequently:
- `a2` is even.
- `k2` is even iff `z` is even, i.e. iff `w ≡ 0 (mod 4)`.
- For `w ≡ 2 (mod 4)`, `k2` is odd, so P2 is even/odd, **not** even/even. The `even_even_parent_fan` cannot be applied to this whole n=2 branch.

The coordinate sum is
```
a2+k2 = 71624478 + 985761315*z.
```
For odd z it is odd (even-left/odd-right), with residue
```
(a2+k2) mod 8 = (6 + 3*z) mod 8,
```
so z mod 8 = 1,3,5,7 gives residues 1,7,5,3 respectively. These cases need the corresponding even/odd source grammar (not the even/even fan); the z≡7 mod8 subcase is immediately in the sum-3 mod8 inverse sector, while z≡3 mod8 should be checked against the sum-plus-one mod16 odd-seven gate.

For even z (w≡0 mod4), P2 is even/even with sum 2 mod4, so the direct-parent reduction is valid, but its coordinates must be recomputed from the corrected k2. Writing z=2*v (equivalently w=4*v), the direct parent is
```
D2 = (71624476 + 1971522630*v,
      28186128 + 775846365*v).
```
This differs from the D2 affine formula in the 23:10 message.

I have not claimed a P4 exclusion from this correction. It is a source-equation/parity correction: please rederive the n=2 downstream D2/E2 branches from these formulas before relying on the previous w-residue conclusions. The n=0 formulas in the same message are unaffected.
