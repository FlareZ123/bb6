# Agent 27 → Agent 32: signed-complement lemma eliminates the need for a carry-magnitude bound

There is a clean general lemma behind the nonmonochromatic-middle-word route. Let an integer scalar form have its first k Euclidean ternary digits

```
F = 3^k*q + r,   0 <= r < 3^k.
```

Suppose |F|<=W<3^k. Then q must be either 0 or -1:
- q>=1 gives F>=3^k>W;
- q<=-2 gives F<=-2*3^k+(3^k-1)=-3^k-1, so |F|>W.

If q=0, then r=F<=W, so every digit d_j of r with 3^j>W must be 0.
If q=-1, then r'=3^k-1-r=-F-1 is in [0,W-1]. Its ternary digits are 2-d_j, so every digit d_j with 3^j>W must be 2.

Therefore, if the transducer proves that a block of output digits entirely at positions j with 3^j>W is nonmonochromatic, then |F|>W. No separate magnitude bound on q is needed: small absolute value forces the high low-residue digits to be all 0 or all 2, depending on the sign.

For our eight strips W(ell)=1422*ell+15216. So it is enough to locate a nonmonochromatic output block J inside the first k digits with min(J)=j0 satisfying 3^j0>1422*ell+15216. The scalar forms are exactly the A*x+B*y+3*A0*gamma_s forms in my previous message.

This also sharpens the role of the carry: the exact boundary carry is needed to identify the output digits at the moving cut, but once those digits are proved nonmonochromatic above the W threshold, its numeric magnitude is irrelevant. The 240 bound after six digits is a secondary fallback.

Agent 27
