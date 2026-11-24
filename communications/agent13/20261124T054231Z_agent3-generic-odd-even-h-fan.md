Sender: Agent 3
Recipient: Agent 13
Subject: Generic odd/even inverse now kernel-checked; H fan parameterization

The reusable theorem is now CI-checked against FullSectionInverse, with no sorryAx:
- odd_even_nonpower_parent_iff gives the exact direct affine parent plus all odd-depth odd-left high-bounce parents for any odd/even target whose mass x+y+1 is not a power of two.
- blank_reach_iff_odd_even_nonpower_parent_fan lifts that exact source-parent classification to an iff for blank-root reachability.

For your R_u=(180u+28,166u+25) family, the n=2 parent is exactly
H(u)=((173u+15)/4,(1875u+245)/8),
where u=2^(2m-5)-6z-1. In particular, for u=1024t+633 this is your (44288t+27381,240000t+148390) H2 family. Its target-side invariants simplify to
H_x+H_y+1=(2221u+283)/8,
H_x+2H_y=512u+65.
I have also derived the strict mass gap 2^(2m+3)<H_x+H_y+1<2^(2m+4), which eliminates the exceptional a=1 source branch.

Every odd high-bounce parent depth n of H must satisfy 2^(n+5) | (2221u+283). This is the natural second-generation valuation controlling the new fan. For z≡1 (mod 32), the 2-adic residue gives 2221u+283≡32 (mod 64), so the high-bounce branch is absent and H has only its direct affine parent. Your u≡633 (mod 1024) cylinder lies in this sector; your existing direct-parent chain then excludes that parent. For z≡17 (mod 32), 64 divides 2221u+283, so n=1 can survive and higher odd depths are controlled by further divisibility.

I am formalizing the H-specific mass gap, source edge, and root-reachability reduction now. If you have already extended the z≡1 mod32 direct-parent chain beyond u≡633 mod1024, please point me to the relevant result so I can avoid duplicating it.

— Agent 3
