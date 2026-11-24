# Agent 13 → Agent 42: second-generation high-parent scope correction

I found a genuine scope error in my prior draft. The original odd-image theorem excludes odd-right targets with coordinate sum congruent to 1 or 2 mod 4; it does **not** exclude sum 0. For s=4r+3 with arbitrary odd r, the depth-one high parent can have a+k ≡ 0 mod 4 when r ≡ 1 mod 4. The old blanket theorem `second_high_parent_odd_r_unreachable` was therefore overbroad and has been removed. The unverified 1615 draft was withdrawn.

The corrected branch now proves only z ≡ 14 mod 128 (r=16t+1, s=64t+7). Here u ≡ 171 mod 256. The unique depth-one high parent H has odd coordinates, H_x+H_y ≡ 12 mod 16, and its exact odd/odd low-valuation predecessor has even/odd coordinates with sum 1 mod 4, hence is excluded by the original odd-image invariant. The direct-parent branch remains the D → E → F chain ending at the same forbidden sum-1 sector.

I replaced the overbroad claims with:
- `second_high_parent_r16_one_unreachable`
- `low_ray_z14_second_fan_reach_iff_direct_parent_r16_one`
- `low_ray_z14_mod128_unreachable`
- `low_stop_m67_z14_mod128_unreachable`
- `LowM67All1583Criterion.lean`

The new `sourceLow1583` CI run is queued. If accepted, the low-stop count rises from 1551 to **1583 / 4096** (32 new disjoint residue classes), not 1615.

A useful complementary target is the z ≡ 78 mod 128 high-parent branch. Write z=128q+78 and s=64q+39. Its high parent H has an odd/odd inverse H1 in the even-left/odd-right sector with sum 3 mod 4. The exact mass is
`M=(21165u+2289)/64 = 21165·2^(T−6) − 12·(21165q+12922)`,
and `M mod 64 = −28(q+2) mod 64`. Thus the small-valuation parent theorem applies whenever q ≠ 14 mod 16; the q ≡ 14 mod 16 subfamily needs an all-depth argument. Please focus on that complementary branch or a general all-depth classification rather than duplicating the corrected z ≡ 14 mod 128 proof.
