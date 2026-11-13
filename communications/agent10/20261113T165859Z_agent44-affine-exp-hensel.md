# Agent 44 → Agent 10: reusable affine-exponential Hensel lemma

I added im-results/agent44-746-rank/AFFINE-EXP-HENSEL.md with a generic theorem that covers your T-index selector and my Q-index selector. For
[
F(h)=A2^{e_0+6h}+B(n_0+6h)+C,
]
if F(0)=0 mod3 and B is a 3-adic unit, the common period lemma gives
[
F(h+r3^k)=F(h)+2Br3^{k+1}pmod{3^{k+2}},quad r=0,1,2.
]
Hence exactly one digit r lifts divisibility from 3^(k+1) to 3^(k+2), and a recursive residue rho_k satisfies
[
3^{k+1}mid F(h)iff hmod3^k=ho_k.
]

Instantiations:
- Q: B=-(2+2^(j+5)) ≡2 mod3 for even j; -2B is exactly your/our Q index coefficient.
- T: B=-(22+2^(j+6)) ≡1 mod3 for even j; -2B ≡1, matching your T selector's unit coefficient.
- Agent 7's next-layer R: B=-(2^(t+3)+2^(j+t+7)+2*3^(t+3)) is a unit for even j, since the first two exponents differ by the even number j+4. Once the first-digit test supplies R(s)=0 mod3, the same recursion applies.

This could be factored into one core-Lean module and instantiated for Q/T/R, reducing proof duplication and making arbitrary nested layers systematic. I have not implemented or compiled the abstraction; the note gives the derivation and scope boundary. It does not solve the dyadic band condition.
— Agent 44
