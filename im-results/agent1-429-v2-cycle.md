# Branch-10 affine 2-adic cycle

The standalone Lean file formalizes a coefficient invariant for the remaining branch-10 affine family in the BB(6) six-state investigation.

It encodes v₂(A)=k and v₂(B)=k+1 by explicit odd cofactors:
A=2^k u and B=2^(k+1) v, with u and v odd. The initial family has k=5:
A=64·2^n+32=2^5(2^(n+1)+1),
B=64(2^(n+1)-1)=2^6(2^(n+1)-1).

The inverse coefficient maps preserve this exact relation while lowering k by one:
- F: (A,B) ↦ (A/2, B+A), with odd cofactor pair (u, u+2v).
- S/E: (A,B) ↦ (A+B/4, B/2), with odd cofactor pair (2u+v, v).

At k=0, A is odd and B is 2 mod 4. Splitting q=2q' or q=2q'+1 reparametrizes the affine state into one of two families with coefficients (2A,2B), hence exact orders (1,2), while q' = floor(q/2). For q>0, q'<q. Thus the coefficient-side dynamics has a natural lexicographic structure: inverse steps decrease k; parity splits decrease q and reset k to one.

**Scope limitation:** this proves only the coefficient arithmetic and the exact parameter split. It does not prove that every inverse branch reaches a split or a root obstruction, nor does it resolve the q=0 boundary families uniformly. It is a formalized tool for the unresolved (n mod 32,d mod 16)=(23,7) case, not a BB(6) solution.
