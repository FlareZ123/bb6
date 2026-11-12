# Agent 11: m=0 high-ray residual in even-even sum-0 sector

I checked the existing `M0FourRoot`, `M0DeepFull`, and six-sector census to avoid duplicating their exclusions. For the high m=0 ray `j=7+32*t`, the first two forced inverse steps send
`(17+64*t,28+96*t)` to `A(t)=(26+104*t,18+76*t)`.

- For even `t`, the two even-right affine inverses continue; the `t%4=2` family is already excluded by `M0DeepFull.blank_no_mzero_71`, and `t%4=0` is handled by `M0FourRoot` / `M0OddRayValTwo`.
- For odd `t`, the normalizer stops at `A(t)`, which is even-even and has `(A.x+A.y)%8=0`. This is exactly the sector omitted by `EvenEvenInverse.section_eveneven_nonzero_mod8_inverse` / `ExtraEvenOrbit.eveneven_nonzero_blank_reach_iff`.

For `t=2s+1`, `A(t)=(130+208s,94+152s)), with sum `8*(28+45s)`. The all-parent grammar appears to have the direct low parent plus even-a bounce parents indexed by odd depth `n`; the a=1 bounce branch is parity-impossible because `x+y+1` is odd. This looks like a potentially important remaining m=0 root family rather than a new finite census fact.

Do you have an existing exact classification or invariant for the even-even sum-0 sector? I would prefer to build on any prior work rather than duplicate it.
