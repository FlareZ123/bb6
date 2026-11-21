# Agent 46 adversarial review: wider second-level residue cut

I checked the displayed proof in `SecondLevelWideResidueCut.md` line by line, and inspected `second_level_wide_residue_cut.js` against the two-step formulas. I found **no mathematical counterexample or algebraic error** in the stated theorem or its exception bound.

The key identities check:

1. With (m=2r-1\ge99), (n=3^m) is odd and (d) is its bit length. Thus (2^d-n) is positive odd. It cannot be 1 because (3^m+1=4(3^{m-1}-3^{m-2}+\cdots-3+1)) has an odd factor greater than 1; it cannot be 3 because (3^m+3) is divisible by 3 whereas (2^d) is not. Hence (2^d\ge n+5).

2. The parent equation gives (D\mid 2y-2w+3). Multiplication by 55 and (w=a+s-1) give (D\mid16AP_r(A)-C), with (C=55\cdot9^r+110s-50). The recurrence expands to (AP_r(A)=\sum_{i=0}^{2r-1}(-3)^iA^{2r-i}). Since (At\equiv-3\pmod D), multiplication by (t^{2r}) gives (t^{2r}AP_r(A)\equiv3^{2r}S=3nS\pmod D). So the sign and coefficient (48n) in (Q=Ct^{2r}-48nS) are correct.

3. (Q>0), (16\mid Q), and (D) is odd, so (Q=16Dz_1) with (z_1>0). The first inequality in (3) gives (M\mid2^{2rs-4}); reducing (Dz_1=C2^{2rs-4}-3nS) modulo (M=2^{a+s-4}), with (D\equiv3\pmod M), correctly yields (M\mid z_1+nS). The definition of (L,c) gives (Ls+c=a+s-4), (c\le s), and (L+1\le2r), so the geometric-tail split is valid.

4. From (c\ge d) we have (s\ge d), (t\ge n+5), and
   (R=n\sum_{i=0}^L t^i<(n+1)t^L\le(2^c-2^{c-d+2})t^L=M-2^{h+2}t^L).
   The second inequality in (3) gives (E+c\ge2d+6), hence (E+h+2\ge d+8). Also (s<a/2) and (C=165n+110s-50<165n+55a<256(n+5)\le2^{E+h+2}). Thus (z_1<2^{h+2}t^L). The final strict interval (0<z_1+R<M) follows.

5. For an exception, (e=c-1=((a-5)\bmod s)) and (a-5=ks+e). The interval gives (r-1\le k\le2r-2), and (0\le e\le d-2). Each pair ((k,e)) determines at most one (s), so the (r(d-1)) upper bound is valid. In this progression (s\ge a/(2r-1)\gg d), so the enumerator's (e<s) condition is automatic; adding an explicit sentence to that effect would make the correspondence completely transparent.

The audit script also matches the two-step note:
- `yMod(r,a,m)` computes (y\bmod m) correctly by running the defining (P_r) recurrence modulo (55m), then dividing the resulting multiple of 55.
- Its `H` residue is exactly (2^{w+2}(y+3-w-t)+9-6t\pmod{D_t}).
- Its `J` residue is exactly (2^{w+1}(4y-4w+27-10t)+63-30t\pmod{D_t}), the one-step-odd-block/even-parent necessary condition.
- The prime filter only rejects when (p\mid D_w) and the parent equation fails modulo (p), which is a valid necessary filter.

I therefore regard the displayed residue-cut theorem and the finite exception parametrization as sound **paper-level arithmetic**. This review is not a Lean compile, source-connected certificate, or blank-root result. The script's survivors remain candidate residue classes, not actual parents or reachable states.

— Agent 46
