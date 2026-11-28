# Space Needle: cancellation indices 10, 11 and 12, complete finite reverse trees

## Result and status

The tenth, eleventh and twelfth cancellation feeders are not on the blank-root orbit, by the established exact shifted-counter inverse correspondence, the kernel-checked arithmetic cancellation cutoff and resonance/gap lemmas, and the finite exact GMP calculation below. This is an intermediate computational exclusion, not a newly kernel-certified finite result or a decision of Space Needle. The previously audited r=7,8,9 cases are not rerun.

For the detailed r=10 audit, set N=9^10=3486784401, a=(N+5)/2=1743392203, A=2^a, M=20a=34867844060, P=(A^20-N)/(A+3). The cancellation feeder b=AP/2 maps to terminal 2^(M-1). We avoid allocating AP or the terminal integer.

## Complete candidate coverage

A reverse node has 2Lb=c AP+d, with c a positive power of two, d even, L positive odd coprime to 3. For m=v+1, D=2^m+3, C=d+L(5-2m), the exact inverse condition is LD | c AP+C with quotient odd and at least 3. The successor representation in the reverse tree is (2^m c,2^m C,LD). The quotient is odd by parity. The program checks positivity by 3LD+|C|<2^(M-1)<AP. The same bound with 6L+|d| excludes the blank root 3. All reverse edges strictly decrease, so the physical range m<=M suffices.

At the initial feeder use the established theorem m^2<16ra, r=10 (see [SharpenedRotationBound](../agent20-needle-coprime/SharpenedRotationBound.md)). This gives m<=528150.

At every proper reverse node c is even, while C and C-cN are odd. Multiplying the parent condition by A+3 gives D | G, where
```
G = c 2^E + (C-cN)2^a + 3C, E=M+a.
```
Let Cmax=|d|+L(2M+5), H=bitlength(c(N+1)+4Cmax), and B(m)=H+2ceil(E/m). The coefficient mass of G is <2^H. The existing generic rotation/resonance theorem (RotationCore.lean, RotationValuation.lean in Agent20's dossier) implies for m>=3B(m) that two of the adjusted exponent residues E+v2(c), a, 0 agree mod m. Thus beyond the greatest m with m<3B(m), the ONLY candidates divide E+v2(c), a, or E-a+v2(c). The monotone threshold is found by binary search; all divisor candidates in [cut+1,M] are enumerated by trial division through the square root. No reliance on the older paper affine cutoff is required for proper descendants.

For ordinary candidates, primes <=10000 supply exact rejection witnesses. Remaining candidates are tested with the three-term congruence: replace each 2^e by (-3)^floor(e/m)2^(e mod m), then repeatedly write S=hi*2^m+lo (signed truncation) and replace S by lo-3hi. This preserves residue modulo D. For m>=8 it terminates because each fold reduces |S| when |S|>=2^m; the final |S|<2^m<D. Small m uses GMP directly. All survivors undergo the original LD divisibility test using modular evaluation of P_r=A^2 P_(r-1)+9^(r-1)(A-3). This test is not replaced by the necessary three-term test.

For large resonant candidates, choose h from {0,B,2B} so all three rotated exponents are <=m-B, using the existing good-shift theorem. The coefficient mass is <2^B; hence divisibility implies the rotated sparse sum is zero. Sort terms by exponent. Between successive exponents e_i<=e_(i+1), the current low accumulator must be divisible by 2^(e_(i+1)-e_i) if the sum is zero. Divide exactly and add the next coefficient. The final accumulator must be zero; the test is equivalent to zero by successive factoring. This avoids allocating giant binary shifts.

Every proper descendant has one candidate m=a passing this necessary three-term test. Apply the same good-shift argument to the ORIGINAL sparse polynomial C+c sum_(j=1)^(2r) (-3)^(2r-j)2^(ja), with H2=bitlength(c(N-1)/2+Cmax), B2=H2+2ceil(M/m), and (2r+1)B2<=m. Its rotated sum is nonzero for all ten such candidates, so they are rejected without constructing giant D. The code explicitly signals unresolved large candidates if neither rejection succeeds and exact modular checking is unavailable. No such unresolved candidate occurred in this audit.

## Exact audit (r=10)

All ranges [1,25000] and [25001,cut] were completed for every listed node. The latter also checks all resonance extras. Counts below aggregate the two ranges. Paths list reverse valuations v=m-1.

| Path | c | d | L | cut | prime rejects | sparse rejects | full LD checks | extras | parent valuations |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---|
| root | 1 | 0 | 1 | 528150 | 429991 | 98158 | 1 | 0 | 4 |
| 4 | 32 | -160 | 35 | 468755 | 298402 | 170349 | 4 | 12 | 1 |
| 4/1 | 128 | -500 | 245 | 468755 | 298427 | 170323 | 5 | 24 | 2,5 |
| 4/1/2 | 1024 | -5960 | 2695 | 468761 | 279719 | 189038 | 4 | 33 | 0 |
| 4/1/2/0 | 2048 | 4250 | 13475 | 468767 | 279712 | 189051 | 4 | 7 | none |
| 4/1/5 | 8192 | -141760 | 16415 | 468767 | 296210 | 172552 | 5 | 18 | 2 |
| 4/1/5/2 | 65536 | -1265400 | 180565 | 468773 | 276079 | 192688 | 6 | 24 | 2 |
| 4/1/5/2/2 | 524288 | -11567720 | 1986215 | 468776 | 276102 | 192669 | 5 | 22 | 0 |
| 4/1/5/2/2/0 | 1048576 | -11218150 | 9931075 | 468779 | 276127 | 192646 | 6 | 15 | 3 |
| 4/1/5/2/2/0/3 | 16777216 | -656182000 | 188690425 | 468785 | 268567 | 200212 | 6 | 36 | 0 |
| 4/1/5/2/2/0/3/0 | 33554432 | -180221450 | 943452125 | 468791 | 268742 | 200043 | 6 | 68 | none |
| TOTAL | | | | 5215859 | 3248078 | 1967729 | 52 | 259 | 10 edges |

Eleven vertices, ten edges, two leaves, zero root matches, zero unresolved large candidates. Ordinary candidate partition holds on every row. No arbitrary valuation cutoff has been substituted for a proved coverage bound.

## Eleventh cancellation feeder

For r=11 the kernel-checked initial cutoff is m^2<16ra, giving m<=1661786. The optimized exact solver rejects the complete interval, including the lower range where the earlier GMP modular exponentiation was expensive.

| Inclusive range | prime rejects | sparse rejects | full LD checks | parents |
|---|---:|---:|---:|---|
| 1..25000 | 20156 | 4844 | 0 | none |
| 25001..50000 | 20210 | 4790 | 0 | none |
| 50001..200000 | 121287 | 28713 | 0 | none |
| 200001..300000 | 80812 | 19188 | 0 | none |
| 300001..600000 | 242609 | 57391 | 0 | none |
| 600001..1000000 | 323494 | 76506 | 0 | none |
| 1000001..1661786 | 535129 | 126657 | 0 | none |
| TOTAL | 1343697 | 318089 | 0 | none |

The r=11 reverse tree consists of its sole root, which differs from blank root 3.

The new needle11.cpp differs from the checked r=10 version only in the specialized modular exponentiation. It replaces general GMP modulus by signed shift folding using 2^m=-3 mod D, after every square and multiplication by 3. Every fold preserves congruence and strictly reduces magnitude whenever |S|>=2^m and m>=8. For smaller m the original GMP path remains. This permits exact modular powers without large general integer division. The exact source SHA256 is ee7f5216b0cce8ab029630ed84d364655296b1772f59b3c5f60e2901a443f592. The first small chunk was also independently repeated with this source. The optimized r=11 calculation is complete, but not yet a Lean finite certificate.

## Twelfth cancellation feeder: complete initial-parent exclusion

For r=12, N=282429536481 and a=141214768243. The same proved cutoff m²<16ra restricts all possible initial incoming valuations to m=1..5,207,037. The existing exact GMP enumerator `needle11.cpp` was executed at pinned revision `ebc7eeb7f62c109d1c4497648f27fd9c93a05a8c` in [manual run 46102294468](https://github.com/FlareZ123/bb6/actions/runs/46102294468), with [raw output artifact 15247340526](https://github.com/FlareZ123/bb6/actions/runs/46102294468/artifacts/15247340526).

```
r=12 c=1 d=0 L=1 range=1..5207037 cut=5207037 sieve=4212546 sparse=994491 exact=0 extras=0 largeZero=0 parents= seconds=1110.07
```

The 4,212,546 prime rejections and 994,491 sparse congruence rejections partition the entire admissible interval exactly. No survivor required a full LD test, and there were no unresolved large candidates. The initial feeder has no predecessor; it is distinct from the blank shifted root 3, so r=12 cannot be encountered on the authentic high-level blank orbit, subject to the same established correspondence, cutoff and exact computational evidence as r=11.

Reproduce with the existing r=11 binary:
```sh
g++ -O3 -std=c++17 -fopenmp needle11.cpp -lgmpxx -lgmp -o needle11
OMP_NUM_THREADS=4 ./needle11 12 1 0 1 1 6000000
```
The source SHA256 remains `ee7f5216b0cce8ab029630ed84d364655296b1772f59b3c5f60e2901a443f592`. This is a finite computational exclusion at one new index, not an all-r result or a kernel-certified finite tree. Agent20 recovered the successful prior computation without repeating it.

## Checked arithmetic implementation

SparseZero.lean independently proves `NeedleSparse.sortCheck_iff`: sorting an arbitrary list of signed coefficient/exponent terms and testing successive binary gaps returns true exactly when their integer sum is zero. If the accumulator is nonzero and the next gap exceeds its log2 magnitude, the implementation rejects without materializing the power. All four exported correctness theorems compile on Lean 4.36.0-rc2 and have only [propext, Classical.choice, Quot.sound]. This certifies the mathematical sparse-zero algorithm, not the C++ binary or the complete r=10/11 audit.

## Reproduce

On 64-bit Linux with GMP and OpenMP:
```sh
g++ -O3 -std=c++17 -fopenmp needle10.cpp -lgmpxx -lgmp -o needle10
OMP_NUM_THREADS=4 python3 reproduce.py
```
The driver traverses from the initial representation, runs both contiguous chunks for each vertex, checks totals, compares each printed child to its affine update and checks the expected tree. Compile without NDEBUG. The exact executed C++ source SHA256 is 9fe23d516e3fd5bad76b52c936ba4ba5a7c3cb0670947b0d4153e8878d1ef6bb.

The integer algorithm and its complete enumeration are computational evidence; the sparse zero algorithm now has a separate checked Lean implementation, but the finite trees have not been ported to a new Lean finite certificate. The original source inverse semantics and cited arithmetic theorems are inherited. A useful next step is to formalize the compact resonance enumeration and extend the audit to further indices or obtain a uniform root-sensitive theorem.
