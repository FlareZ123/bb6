# 20,001-state four-sector root-gap scan

**Agent 49, 2026-11-07. Intermediate computational evidence only.** This
replay starts at the exact blank-root section state D(0,7) and follows the
source-matched evalA, drainB, and highLevelNext equations. It does not
prove an all-time invariant or decide the machine.

## Reproduction

From this directory, with a C++20 compiler and Boost.Multiprecision headers:

~~~sh
g++ -O3 -std=c++20 root_gap_scan.cpp -o root_gap_scan
./root_gap_scan 20000
~~~

The program uses arbitrary-precision integers throughout. It checks each
transition, the sector's sufficient bit-length budget, and the gap
inequalities with exact integer arithmetic. The four sufficient budget tests
are:

- left odd: a-d-5 >= bitLength(d+3)+2;
- left even: a-d-2 >= bitLength(d+2)+2;
- right odd: d+4-a >= bitLength(a-1)+2;
- right even: d+1-a >= bitLength(a)+2.

Here bitLength(x)=Nat.log2(x)+1. The Lean file
[GapBudgetArithmetic.lean](GapBudgetArithmetic.lean) proves that
x.log2+3 <= k implies x <= (3^k-1)/2, and gives the strict version for
positive x. Thus these checks are sufficient to establish membership in the
four-sector exponential newAffineCone for every scanned state.

## Exact finite-scan output

The command above returned:

~~~text
states=20001 checked=9..20000
canonical_min=4096/235 index=16 sector=LO gap=-64 scale=235 a_bits=10 d_bits=8
old_ray_min=676/122 index=13 sector=RE gap=-26 scale=122 a_bits=7 d_bits=9
canonical_tail_min=4096/235 index=16 sector=LO gap=-64 scale=235 a_bits=10 d_bits=8
old_ray_tail_min=5329/235 index=16 sector=LO gap=-73 scale=235 a_bits=10 d_bits=8
max_coordinate_bitlength_difference=16 at_index=6901
~~~

The canonical ratio-four terminal gap is:

- g = a-4d, with scale=d, on left sectors;
- g = d-4a, with scale=a, on right sectors.

The exact scan verifies g^2 >= 5*scale at every index 9 through 20,000.
From index 16 onward it verifies the stronger g^2 >= 17*scale; the exact
minimum ratio is 4096/235 at D(876,235).

For comparison, the conventional old-ray distance extended to all four
sectors is:

- left odd: h = a-4d-9;
- left even: h = a-4d-5;
- right odd: h = (d-4a-1)/2;
- right even: h = (d-4a-2)/2.

The scan verifies h^2 >= 5*scale throughout indices 9 through 20,000,
with exact minimum 676/122 = 338/61 at index 13, D(122,438). From index
16 onward it verifies h^2 >= 22*scale, with exact minimum 5329/235 at
index 16.

## Interpretation and limitation

The canonical gap is the direct linear form appearing in the source-derived
ratio-four terminal windows. The old-ray distance differs from it by the
displayed fixed offsets and factors. Keep the two conventions distinct.

The 20,001-state scan is a reproducible finite observation. It suggests the
root orbit may obey a strong square-gap invariant, but it supplies no
induction proving that invariant for all future states. The maximum
coordinate-bitlength difference of 16 is another finite diagnostic, not a
global ratio bound. No nonhalting conclusion for #623 follows from this scan.

The next mathematical target is an all-time root-sensitive invariant or a
source-exact block-return argument proving avoidance of the terminal
ratio-four windows. Any proof must account for all four sectors and the
small exceptional prefix.
