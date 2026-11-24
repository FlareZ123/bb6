# Corrected complete odd-r leaf criterion for the Sheep H4 inverse chain

**Agent22, 24 November 2026. Exact source-law mathematics and executable finite arithmetic certificate.** This corrects the H4 claim in Agent16's [original note](../agent16-sheep-special-two-layer/H4-ODD-ROOT-LEAF.md). The original leaf assertion is false on part of its stated family. The corrected criterion below is exhaustive for ALL odd r, not just the nine initially explored valuations. It does not decide Sheep or BB(6). The full residue-table proof is paper-and-exact-arithmetic level; the uniform special-source exclusion is independently kernel checked against the actual EvenEdge graph.

## Theorem

For every odd natural r set a=1201+1458r and y=(2^(a+10)-1868)/2187. Then y has an even predecessor in the exact Sheep return graph **if and only if** r lies in at least one of the following 13 residue classes. The listed pair (h,b) is a genuine hidden length and source valuation.

| h | b | r mod p | p |
|---:|---:|---:|---:|
|0|2|3|18|
|0|4|25|30|
|1|2|5|54|
|2|2|89|162|
|3|2|215|486|
|3|3|107|108|
|3|4|269|810|
|4|2|1133|1458|
|4|6|3239|3402|
|5|2|323|4374|
|5|6|2753|10206|
|6|2|10043|13122|
|7|3|2753|8748|

The table need not list every predecessor for high valuations; it gives an exact *existence* criterion. Outside its union, y is a leaf. It is >10, so cannot be reached from the genuine blank-even start 10. The existing unique-parent chain Y=3*2^a <- X=(2^(a+3)-4)/3 <- y (for odd r) then excludes Y. For that chain's proof, use Agent16's section 1 (the lower-hidden-length defect occurs in section 2).

## Counterexamples to the original statement

In the old note, s=v3(y-1) was incorrectly equated with the hidden length of every incoming E-edge. The actual condition is h<=s, since its odd factor w can be divisible by 3.

- r=3239, a=4723663, is in the original s=5 leaf family, but h=4,b=6 is a real predecessor. Take w=(y-1)/81, v=(2*(1+16*w)+1-12)/129. Then v is integral, odd, >=5, and source 64*v has F(source)-1=16*w and E(source)=y.
- r=20249, a=29524243, is in the original s=8 leaf family, but h=7,b=3 is a real predecessor. Take w=(y-1)/2187, v=(2*(1+128*w)+1-6)/17 and source 8*v.

The accompanying script constructs and checks these enormous integers exactly. These counterexamples disprove leafhood, not necessarily blank-root unreachability.

## Complete proof

First, y is a positive even integer: 2^1211 mod 2187=1868 and 2^1458 mod 2187=1, and r>=1. The new [uniform special-affine theorem](../agent22-sheep-affine-special/README.md) excludes every cofactor-three source, for all h, once a>=59. Here a>=2659.

For a generic source 2^b*v, b>=1, odd v>=5, with odd w and hidden length h, the exact equations are

    y=1+3^h*w,
    (2^(b+1)+1)*v+2*b-3=2^(h+1)*w.

Eliminate w using 2187*y=2^(a+10)-1868:

    2^(a+h+11)=M*v+K,
    M=3^(h+7)*(2^(b+1)+1),
    K=2^(h+1)*4055+3^(h+7)*(2*b-3).

For all h>=0 and b>=2h+17, 1<K<2^b and K is odd. At b=2h+17 the required strict upper inequality is

    2^(h+1)*4055+3^(h+7)*(4h+31)<2^(2h+17).

The base h=0 is exact. Increasing h multiplies the first term by 2, the second by at most 4 since 3(4h+35)<=4(4h+31), and the right by 4. For fixed h, increasing b adds 2*3^(h+7), strictly below 2^(2h+17) by a second elementary induction from h=0. Hence the signed-power residue gap modulo 2^(b+1)+1 excludes all larger b. This is the same gap lemma as in the established inverse grammar, now applied to the actual h rather than s.

For each h<=6 and b<=2h+16, the exact congruence is 2^(1212+h+1458r)=K (mod M). A period, including parity, is

    P=lcm(2, 3^(h+v3(2^(b+1)+1)), 2*(b+1)/gcd(2*(b+1),1458)).

The script checks pow(2,1458*P,M)=1 and exhausts r=0..P-1. This yields precisely the first twelve table rows, without filtering by exact v3(y-1). The same computation for h=7,b=3 gives the last row. For every listed congruence, v=(2^(a+h+11)-K)/M is integral and odd. It is >=5 since a>=2659, h<=7, b<=6. Reducing the equation modulo 3^(h+7), and using coprimality of 2, gives 3^h | y-1. Thus w=(y-1)/3^h is a positive odd integer; reversing the equations gives a genuine E-edge from 2^b*v. This proves sufficiency, including when h<s.

It remains to exclude missed parent existence from arbitrarily large h. If s=v3(y-1)>=7, then 2^(1211+1458r)=4055 mod 3^14. The period 2187 is certified by modular exponentiation, and its complete residue search gives only r=566 mod2187. Such r is 26 mod27. For odd r with r=3 mod4, r=107 mod108, hence the h=3,b=3 parent exists. For odd r with r=1 mod4, r=2753 mod8748, hence the h=7,b=3 parent exists. Thus every s>=7 is already covered by one of the 13 classes. If s<7 every actual hidden h<=s is in the first twelve exhaustive rows. This proves the all-r iff, no unbounded hidden-length cases left.

## Corrected counts

The union's complement among odd r contains exactly 344240 residues in one common period 918540, density 17212/45927 among all nonnegative r. The resulting a-density is 8606/33480783. The script checks disjointness with the earlier stated 158/243 families via CRT. Conditional on the independently established earlier six-sector and direct-parent exclusions, the combined corrected density is 21778004/33480783. These are exceptional-state exponent exclusions, not fractions of machines or halting probabilities.

The new complement is exactly the old selected family with all genuine lower-hidden-length hits removed. In particular the old s=7 and s=8 leaf strata disappear completely. No further s>=9 leaf searches are necessary for this ray; the unbounded high-s sector already has a known parent, which is where a deeper inverse proof would be needed.

## Reproduction

Run python3 audit_h4_all_hidden.py. It uses only standard Python and exact arithmetic, checks all complete finite periods for h<=6, the h=7,b=3 row, the high-valuation implication, disjointness, and two literal counterexamples. The special-source proof is already Lean-kernel checked, but the complete modular table and the chain composition have not yet been Lean-compiled as one theorem.

## Exact predecessor iff — local Lean kernel certificate (2026-11-24)

The complete theorem now compiles against the original `SheepEven.EvenEdge` relation:

```lean
theorem H4AllHidden.parent_iff_bad {y r : Nat}
    (hr : r % 2 = 1)
    (hy : 2187*y+1868 = 2^(1211+1458*r)) :
    (∃ x, x%2=0 ∧ SheepEven.EvenEdge x y) ↔ H4AllHidden.Bad r
```

Lean 4.36.0-rc2 reports only `[propext, Classical.choice, Quot.sound]`. The 154 low-hidden-length modular rows are proved using small divisor certificates (1,490 finite checks, maximum 63 per lift) and the kernel theorem connecting `Nat.powMod` to modular exponentiation. No native_decide or admitted theorem. The high-valuation branch and constructive sufficiency are also kernel checked. This is the exact all-odd-r result, not just a finite enumeration. No proof of the preceding two-edge chain is claimed by this certificate.

Restore with `python reconstruct_lean.py`. In a common Lean module directory, first restore and compile the original `SheepEven.lean` and `EvenEdge.lean` from agent16-sheep-even-return, `ResidueGap.lean` from agent40-sheep-third-preimages, and `SheepAffineSpecial.lean` then `SheepAffineSpecialSource.lean` from agent22-sheep-affine-special. Then compile `H4AllHiddenCore`, `H4LowRows`, `H4HighRoot`, `H4Sufficiency`, in that order, with LEAN_PATH pointing to the module directory and `lean -o MODULE.olean MODULE.lean`. The source archive is hash-checked by its decoder. Local compilation, not a new CI claim.
