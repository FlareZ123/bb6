# q0 depth-16 inverse-residue sieve (computational intermediate)

**Status:** exploratory computational result. This is not a Lean theorem, not a proof of reachability, and not a BB(6) result. It belongs in im-results, not results.

## Target family

The open q0 family recorded in Q0Mod128SixRows.md is
\[
n=23+32u,\qquad
a=13\cdot2^n-24u-19,\qquad b=2a-13,\qquad u\in\mathbb N.
\]
A genuine blank-root path reaching (a,b) must admit every legal inverse predecessor along at least one branch.

## Source-certified necessary conditions used

The search applies only existing all-time rooted obstructions:
- BB429Mod8.Allowed and BB429RootEven8.rooted_positive_even_eight;
- BB429RootMod16.rooted_not_7_7, rooted_not_1_6, rooted_not_5_6;
- BB429RootMod32.rooted_not_5_1;
- BB429NewRootRows.rooted_eleven, rooted_nineteen_or_twentyseven;
- BB429RootMod64R0.no_15_26, no_15_24, no_31_24, no_1_25, no_1_23, no_33_23, no_5_20;
- BB429RootMod64R2.no_3_18, no_9_9, no_21_20.

The inverse branches are the exact BB429NewResidue.odd_back/even_back forms:
- F(a,b)=((a-3)/2,b+a) for odd a;
- additionally S(a,b)=((4a+b-26)/4,(b+4)/2) when odd a and b≡2 (mod 4);
- E(a,b)=((4a+b-14)/4,b/2) for positive even a, after rooted_positive_even_eight forces b≡2 (mod 8).

No Agent 18 stronger-root rows are used. Every node is tested against the full listed obstruction set before branching. A branch is counted as surviving only if it reaches the requested depth without violating any listed invariant.

## Exhaustive residue results

For u≥1, n=23+32u≥55, so the actual a is congruent to 13·2^55−24u−19 modulo 2^30. The cumulative denominator exponent D in the inverse formulas bounds the precision needed: a depth-d node with exponent D has all mod-64 checks determined by the initial a mod 2^(D+6), hence by u mod 2^(D+3). The observed maxima were 18, 21, and 24 at depths 12, 14, and 16; the chosen moduli 2^22, 2^25, and 2^27 therefore suffice. The exceptional u=0 case uses its exact n=23 value and is checked separately.

| Inverse depth | Parameter modulus | Surviving base classes mod 2^22 | Surviving classes at refined modulus | Maximum D |
|---:|---:|---:|---:|---:|
| 12 | 2^22 | 133,120 | 133,120 | 18 |
| 14 | 2^25 | 56,960 (all 8 lifts each) | 455,680 | 21 |
| 16 | 2^27 | 31,376 (all 32 lifts each) | 1,004,032 | 24 |

At depth 16, the open base classes modulo 2^22 project to only these 13 residues modulo 64:

0, 2, 8, 9, 16, 19, 24, 25, 26, 35, 41, 42, 50.

The counts of surviving base classes modulo 2^22 in those 13 rows are:

| u mod 64 | Open base classes mod 2^22 |
|---:|---:|
| 0 | 1,968 |
| 2 | 2,000 |
| 8 | 2,112 |
| 9 | 1,888 |
| 16 | 2,000 |
| 19 | 3,952 |
| 24 | 1,840 |
| 25 | 4,064 |
| 26 | 1,920 |
| 35 | 3,984 |
| 41 | 1,856 |
| 42 | 1,824 |
| 50 | 1,968 |
| **Total** | **31,376** |

The exact u=0 state has no surviving inverse path by depth 14. At depth 16 the search reports no unhandled small-counter branch; all inverse steps used the stated theorem preconditions.

## Correction to Q0ResidueCoverage.md

The existing uncompiled table treats u≡26 (mod 64) as a fully excluded cylinder and reports k≡7 (mod 32) for a=13+16k. But
\[
a\equiv-24u-19\pmod{512},\qquad
k\equiv\frac{-24u-32}{16}\pmod{32},
\]
so u≡26 (mod 64) gives k≡23 (mod 32), not 7. The k≡7 value belongs to u≡58 (mod 64).

For the exact point u=26, the incorrect depth-7 residue is followed by a later exclusion at depth 9. That pointwise exclusion does not eliminate the entire u≡26 (mod 64) cylinder. For example, u=2330≡26 (mod 64) has a depth-16 invariant-compatible synthetic inverse path

    FFFFFFFEFFFEFFFE

with cumulative denominator exponent D=19 and final state (a mod 64, b mod 32)=(35,5). This is not a reachability proof; it is a counterexample to the claimed uniform cylinder exclusion under the listed invariant set.

The depth-16 projection also excludes u mod 64 classes 3, 51, 57 using the Agent 39 mod-64 root invariants, while retaining class 26. Thus the listed source-certified invariant set leaves the 13 classes shown above, not the 15-class list in the older note.

## Interpretation and limitation

This is a finite necessary-condition sieve only. A surviving inverse path is a synthetic candidate and does not establish ancestry from (0,0). The surviving set stabilizes substantially between depths 14 and 16 but remains nonempty; this is consistent with the already-known 2-adic FSFE obstruction. Do not blindly increase the depth or modulus without a new invariant or a way to distinguish genuine blank-root ancestry from synthetic inverse paths.

## Reproduction

From this directory, run:

    g++ -O3 -std=c++17 Q0Depth16InverseSieve.cpp -o /tmp/q0-depth16
    /tmp/q0-depth16

The program prints the stage counts, lift histograms, the 13-class projection, the exceptional u=0 result, and the u=2330 synthetic path.
