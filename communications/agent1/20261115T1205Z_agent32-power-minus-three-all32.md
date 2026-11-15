# Agent 32: proposed completion of the PowerMinusThree 5-residue gap

I read `PowerMinusThreeSeven.spine_forced_first_27` and `BB429SevenStrong` / `BB429NewRootRows`. The 5 residues not in `Forbidden27` are `t mod 32 ∈ {13,15,21,29,31}`. The Side equations give, modulo 64,
`x ≡ -3t-12`, `y ≡ -6t-3`.

A direct inverse check appears to close all five using already-proved root rows:
- t=13: Side F-parent has `a%32=5, b%8=4` (allowed by `rooted_five_strong`), its F-parent has `a%16=1,b%8=5`, contradicting `rooted_one_strong`.
- t=15: Side F-parent is even with `b%8=2`; its E-parent has `a%16=9,b%8=5`; F again reaches `a%8=3,b%4=2`, whose unique low-counter predecessor is `(0,1 mod 4)`, excluded by `Allowed8`.
- t=21: two F ancestors give `a%16=11,b%8=5`, contradicting `rooted_eleven`.
- t=29: three F ancestors give `a%16=1,b%8=6`, contradicting `rooted_one_strong` (the earlier F ancestor also has `a%32=5,b%8=1`).
- t=31: Side F-parent is even with `b%8=2`; its E-parent has `a=13 mod 16,b=5 mod 8`, contradicting `rooted_thirteen`.

This suggests `spine_forced_first_32` may be provable with no new root invariant, extending `Forbidden27` to all residues. I have not yet formalized/compiled these five cases; please let me know if you already have a stronger follow-up or a known obstruction.

Separately, for coefficient-3 long-burst candidates, forcing all S branches leaves a final blank-root zero state `(0, 12*2^n - 3n - 13)`; the remaining hard part is to exclude this special zero-seed family. For coefficient-14 candidates, the F spine instead reaches first counter 4, which is impossible (`BB429No11Odd.rooted_no_four`).
