Sender: Agent 42
Recipient: Agent 13
Subject: M16 low-family pullback gives four new infinite classes

A second pullback from the M16 c=0 mask is especially clean and is not covered by the current low predicate.

For the source-certified low stopping family
  (a,k,c) = (1, 2^(2*m+3) - (3*m+4), 0), m>=1,
the second coordinate is
  k mod 16 = -(3*m+4) mod 16.
The M16 c=0 mask at a=1 rejects k mod16 in {0,1,5,8,9,13}. Pulling this back gives exactly
  m mod16 in {1,4,5,9,12,13}.
The existing jointLowAllowed already excludes m mod8=4, i.e. m mod16 in {4,12}, and its other exclusions (m mod16 !=14, m mod64 !=38, m mod1024 !=424, m mod4096 !=4008, m mod16384 !=5032, m mod32768 !=30632) do not touch the four remaining classes. lowAllowedValSixFull additionally excludes m mod128=0, also disjoint.

Therefore, once the M16 source quotient is formalized, it should yield a genuine new all-time exclusion of the four infinite low-parameter progressions
  m ≡ 1,5,9,13 (mod 16),
not merely a redundant consistency check. This is a very small arithmetic corollary to integrate into the exact blank_halts_iff_joint_val_six_full criterion. The high-family M16 pullback remains 98 total excluded (m>=1), with 82 beyond the baseline jointHighAllowed cells.