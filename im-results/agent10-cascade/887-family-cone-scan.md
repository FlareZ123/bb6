# Higher 3-adic branches in the 887 feeder family

**Status:** exploratory exact-arithmetic computation; not a Lean theorem and not a blank-root exclusion.

## Why the fixed cone is not a family certificate

`Z1Z2Cone887.lean` gives a 10-state closed reverse cone for the single target at n=887. That finite certificate must not be silently generalized to all n congruent to 887 modulo 13122. The exact ResetParent equations allow additional odd-parent branches when a deeper 3-adic valuation occurs.

For n=887+13122r, put p=2^(n-2), T=80p-4118n-6123, and

    z2(n) = 12(T/243) - (2p+n+1).

Following the common branch from z2 through four even parents at dyadic index n-4, then two odd parents with valuation t=0 at indices n-5 and n-6, defines a feeder height h(n). Direct algebra gives the candidate identity

    729(2h(n)+5) = 463p - 8517418n - 12409413.

The exact odd ResetParent arm at h uses 2h+5=3^(t+1)d with d odd and the band 6·2^k+1 ≤ 2^t d ≤ 8·2^k-1. Thus higher values of v3(2h+5) can create additional parents beyond the t=0 branch.

## Reproducible samples

The accompanying `scan_887_family_cones.py` transcribes the two exact ResetParent equations from `FirstInverseComplete.lean`, enumerates all parents using the dyadic band, and computes the full reverse cone from z2(n). For r=0 through 20 it reports:

| r | n | reverse-cone nodes | max depth | v3(2h+5) |
|---:|---:|---:|---:|---:|
| 0 | 887 | 10 | 7 | 2 |
| 1 | 14009 | 11 | 7 | 3 |
| 4 | 53375 | 11 | 7 | 4 |
| 7 | 92741 | 11 | 7 | 3 |
| 10 | 132107 | 11 | 7 | 3 |
| 13 | 171473 | 14 | 9 | 7 |
| 16 | 210839 | 11 | 7 | 3 |
| 19 | 250205 | 11 | 7 | 3 |

At n=14009 the feeder h has an extra odd parent with t=2. At n=171473 it has additional t=2 and t=5 parents; the t=5 branch itself has a two-edge continuation. The sample therefore falsifies the naive claim that the exact 10-state n=887 cone is automatically a uniform cone for the entire n≡887 (mod 13122) family.

The Python computation is discovery evidence only. It should be checked against `parentsFast` / `ResetParent` in Lean before being used in a proof. In particular, no assertion is made here that the sampled finite cones establish an all-family result.

## Mathematical next step

Study the one-variable 3-adic function

    F(r) = 463·2^(885+13122r) - 8517418(887+13122r) - 12409413.

The observed extra branches are controlled by v3(F(r))-6. Since 2^13122 ≡ 1 (mod 3^9), while the linear term changes by a unit multiple of 3^8 when r increases by 1, F has a natural Hensel-lift structure: at each precision there is a unique residue class of r producing one additional power of 3. A formal selector for this residue class is a promising way to control the nonuniform branches.

## Related work

- `im-results/agent7-746-even-parent/Z1Z2Cone887.lean` — fixed n=887 cone.
- `im-results/agent10-cascade/Z1UniqueParent887.lean` — uniform first unique-parent step.
- `im-results/agent10-cascade/RayTwoTierDepthHensel.lean` — source-checked all-precision selector for the second-tier depth numerator.
- `im-results/agent10-cascade/FirstInverseComplete.lean` — exact ResetParent relation.