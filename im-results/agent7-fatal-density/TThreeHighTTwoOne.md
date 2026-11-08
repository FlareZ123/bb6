# High-q t=2 branch with quotient d = 1 mod 3

**Status:** intermediate research result. The Lean source modules are committed with a targeted full-source CI check pending. This result is a necessary-condition refinement, not a root-death theorem.

## Setting

Assume the original-source high-q equations used by the existing t=2 analysis, with n >= 20, n mod 6 in {4,5}, and

- 2*ray(n,j)+5 = 81*d0
- 16*d0 = 2^n + q + (n-3) + 5
- 2*q+5 = 81*e
- 16*e = 8*2^(n-6) + r + (n-6) + 5
- 2*r+5 = 27*d
- 8*d = 8*2^(n-8) + a + (n-8) + 5

The existing source bound gives s=2^(n-8), k=n-8, and 1973*s <= 1000*d <= 1979*s. The four exact even predecessor equations produce b,c,f,g:

- 2*a = 8*s + b + k
- 2*b = 8*s + c + k
- 2*c = 8*s + f + k
- 2*f = 8*s + g + k

## New residue structure

For d mod 3 = 1, the source constant satisfies (8*s+k) mod 3 = 1. Reducing the five equations modulo 3 gives

(a,b,c,f,g) mod 3 = (2,0,2,0,2).

The residues at b and f force their actual reset predecessors to be even. At a and c, the existing band_nonine_parent_even theorem gives uniqueness of the even parent whenever 9 does not divide 2*a+5 or 2*c+5, respectively.

Consequently, if both mod-nine gates fail,

- (2*a+5) mod 9 != 0
- (2*c+5) mod 9 != 0

then a rooted a forces b, c, f, and g to be rooted in succession.

The existing four-even geometry places g in the strict even-image gap

- 4*s < g
- 2*g+2 < 12*s.

The exact source gap theorem excludes every even reset predecessor of g at every dyadic scale. If g is rooted, its actual source predecessor must therefore be odd. GapOddParent g records that predecessor with the complete source equations, its odd quotient, and its dyadic image band.

The resulting theorem is high_ttwo_one_root_odd_fork: a rooted t=2 candidate with d mod 3 = 1 implies one of (2*a+5) mod 9 = 0, (2*c+5) mod 9 = 0, or an actual odd source predecessor of g.

## Modulo-9 selector

Combining the two gate conditions with the exact n mod 18 arithmetic gives:

| n mod 18 | d mod 9 allowed without the forced g odd fork |
|---|---|
| 4 or 17 | 1 or 4 |
| 5 or 10 | 4 or 7 |
| 11 or 16 | 1 or 7 |

For the omitted d residue in each row, GapOddParent g is necessary. Equivalently:

- n mod 18 in {4,17}: d mod 9 is 1, 4, or the g odd fork is present.
- n mod 18 in {5,10}: d mod 9 is 4, 7, or the g odd fork is present.
- n mod 18 in {11,16}: d mod 9 is 1, 7, or the g odd fork is present.

The third residue class is not excluded. It is routed into a specific, genuine odd inverse branch at g. This makes the d mod 3 = 1 branch structurally different from the already root-dead d mod 3 = 2 branch and the gate-selected d mod 3 = 0 branch.

## Verification and scope

- TThreeHighTTwoOneArithmetic.lean proves the mod-9 exponent table and residue selector using Lean core arithmetic.
- TThreeHighTTwoOne.lean connects the selector to the original reset-parent source grammar through the existing source theorems.
- The local proof draft was checked against explicitly declared source-interface stubs. That check validates proof structure only.
- Targeted repository CI is required to verify the theorem against the actual imports. The CI result will be recorded in the dossier README after completion.

This result does not establish that any candidate is actually reachable, does not resolve the remaining odd-parent recursion at g, and does not prove that machine #746 halts or fails to halt. It contributes no BB(6) upper bound by itself.
