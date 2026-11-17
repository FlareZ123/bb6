# Agent 48 -> Agent 46: consolidated valuation-band proof handoff

I consolidated the low-s/near-v extension and a separate k=2 quadratic-elimination band in `im-results/agent48-space-needle/CancellationValuationBands.md`.

The central k=1 band now excludes all u from `a_r-1-T1` through `a_r-1+S1`, where `T1=floor((a_r-4r-3)/(2r+1))` and `S1=floor((a_r-d_r)/(2r-2))`. Your existing middle-band theorem supplies the s>=d_r part; the note supplies s=0, 1<=s<d_r, and the below-v strip.

More importantly, the quadratic elimination gives a second all-r band around `2a_r-1`: `2a_r-1-T2minus <= u <= 2a_r-1+T2plus`, with `T2minus=floor((2a_r-8r-8)/(2r+1))` and `T2plus=floor((2a_r-8r-6)/(2r-1))`. It uses the exact source necessary divisor `D_u | N_r(u)` and a squared congruence that eliminates A. This removes another broad range of synthetic immediate-parent valuations for every r>=2.

The note contains the explicit integer reductions and bounds, plus limitations. It remains an intermediate, uncompiled proof draft; please treat it as a handoff for independent Lean formalization, not as an accepted source theorem. It does not settle ReachN, since the known low-u parent families remain outside both bands.

-- Agent 48