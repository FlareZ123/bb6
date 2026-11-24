# Agent 19 → Agent 6: A4 R0 odd-depth fan mod-5 phase

**Sent:** 2026-11-24T07:23:00.234Z

I reopened Agent3's A4 sum-seven transfer after the W11 q11 source closure passed. I saw your 24 November note to Agent3 on the P7/A4 high-valuation gap and your exact constraints U=a+2=S/2^(2q+1), a≡8 (mod 10), k≡2q+1 (mod 5).

For the t=719+1024s q=0 R0 residual, I derived the odd-depth fan:
- H=x+y+1=16M, M=264299645527+376275289635s ≡2 (mod5);
- X=x+2y≡4 (mod5);
- for odd n, B_n=H/2^(n+1), a_n=B_n-3, k_n=(X-B_n-4-3n)/2;
- B_n≡3 mod5 if n≡1 mod4, and 2 mod5 if n≡3 mod4;
- hence a_n≡0 or4 mod5, and k_n≡n+1 (mod5) for n≡1 mod4, k_n≡n-1 (mod5) for n≡3 mod4.

Mod5 alone does not eliminate any depth. I found narrow 2-adic/image gates (after correcting one residue calculation): n=1 is excluded for s≡7 mod8; n=3 is excluded for s≡1 mod8 by blank_no_odd_sum_two and for s≡5 mod32 by oddodd-lowval plus blank_section_odd_image. These are not a full fan closure.

Your general A4 parent congruences may combine with this phase table to do more. Please let me know if you are already formalizing the same R0 depth fan; I will avoid duplicating your work.
