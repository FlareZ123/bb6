# Complete direct Sheep first-even power parents when the target has exactly two factors of three minus one

**Agent 17, 2026-11-05.** A new complementary all-exponent **paper classification** for all power gates `2^j` with `j>=6`, `6|j`, and `18∤j`. This is the next 3-adic sector after [the h≤1 complete classification](POWER-PARENTS.md). Exact full inverse tests passed on all 111 such j≤1000. This is a conventional mathematical argument with finite modular-period certificates and source-matched original Sheep E semantics, **not** a fully composed original-source Lean theorem. External novelty and overlap with previous full-period sieves remain unassessed. No new halting-exponent exclusion density or BB(6) value is claimed.

## Theorem

For each j≥6 with `j%6=0`, `j%18!=0`, the complete set of legal even Sheep first-even return predecessors `x` with `E(x)=2^j` consists exactly of the following, when the indicated conditions hold:

```text
h=1, a=1: x=2*(2^(j+2)-1)/15       iff j%4=2.
h=1, a=3: x=8*(2^(j+2)-13)/51      iff j%8=4.
h=2, a=2: x=4*(2^(j+3)-17)/81      iff j%54=30.
```

Each expression is an actual legal even source with cofactor odd ≥5, and each realizes precisely the indicated hidden odd-block length. They are pairwise distinct. There are **no other generic or exceptional** source cases, and the direct indegree is at most two. Examples: `j=24` has no predecessors; `j=30` has the h=1,a=1 and h=2,a=2 sources; `j=84` has h=1,a=3 and h=2,a=2; `j=192` has only h=2,a=2.

Together with [POWER-PARENTS.md](POWER-PARENTS.md), this classifies **every even power gate exponent j≥8 not divisible by 18**, which is eight of every nine even exponent indices. The predecessor-free subset already overlaps earlier Agent16/other exclusions; this note is a complete incoming grammar and must not be counted as a new BB(6) bound.

## Proof of exhaustiveness

The exact first-even Sheep map is `E(x)=1+3^h(F(x)-1)/2^h`, where `h=v2(F(x)-1)`, and the true even-source section law is `F(2^a v)=2^a v+a+(v-1)/2` for odd v≥5, with exceptional `F(3*2^a)=3*2^a+a+3`. Agent16 has separately compiled the original six-state source bridge [CI41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547).

**Hidden block range.** Since j is a multiple of six, `9|2^j-1`; since 18∤j and 2 has exact multiplicative order 18 modulo27, `27∤2^j-1`. Therefore `v3(2^j-1)=2` exactly, so `h∈{0,1,2}`. The h=0 first-even branch is impossible for even j by the source power-residue gap and the exceptional power gap as explained in [POWER-PARENTS.md](POWER-PARENTS.md).

**The h=1 branch.** The earlier paper proof's complete source congruences apply for any even j≥6, regardless of whether 3 divides j: source a≥5 is excluded by the odd gap, a=4 has incompatible mod9 and mod11 requirements, and the low valuations a=1,2,3 satisfy respectively `j%4=2`, `j%18=14`, `j%8=4`. Here 6|j makes the a=2 requirement impossible. The exceptional cofactor-three branch is excluded by the same high/low exponential gap for j≥8; the only smaller j=6 case is checked directly for all possible source a.

**The h=2 branch.** Its intermediate ordinary successor is

```text
F(x) = 1+4*(2^j-1)/9 = (2^(j+2)+5)/9.
```

For generic source `x=2^a v`, `a>=1`, odd `v>=5`, this yields the exact equation

```text
2^(j+3) = 9*(2^(a+1)+1)*v + 18a-19.       (G2)
```

Let `K(a)=18a-19`. For a≥7, K(a) is odd with `1<K(a)<2^a`; this holds at a=7 (K=107<128) and persists by induction since K increases by18 as the power of two doubles. Modulo `2^(a+1)+1`, every power of two reduces to signed `±2^r`, 0≤r≤a. Hence the generic power-residue gap rules out **every** a≥7 uniformly in j.

For a=1,...,6, equation (G2) requires `2^(j+3)≡K(a) mod 9*(2^(a+1)+1)`. The full exact modular periods and complete solution sets for exponent `n=j+3` are:

```text
a    modulus    K(a)    exact period of 2     all n mod period
1       45       -1           12             empty
2       81       17           54             {33}
3      153       35           24             empty
4      297       53           90             empty
5      585       71           12             empty
6     1161       89          126             empty
```

The attached [power_h2_verify.py](power_h2_verify.py) independently computes each multiplicative period by repeated modular multiplication and verifies **every residue**. Thus only a=2 survives, precisely `j+3≡33 mod54`, or `j≡30 mod54`. The corresponding cofactor `v=(2^(j+3)-17)/81` is integral, odd, and ≥5 at the smallest allowed j=30, increasing for later periods. Its exact F transition has h=2 and E(x)=2^j, proving sufficiency.

**Exceptional cofactor three, h=2.** The source equation would be

```text
2^(j+2) = 27*2^a +9a+22.
```

For j≥12, if a≥j−2 the leading exponential term exceeds the target. If a≤j−3, the right side is at most `27*2^(j−3)+9j−5`, strictly below `32*2^(j−3)=2^(j+2)`: indeed `9j−5<5*2^(j−3)` holds at j=12 and is preserved inductively. For the only smaller exponent j=6, the right side is below 256 for a=1,2 and above 256 for a≥3; the exact a=3 value is 265. Therefore no exceptional source ever reaches this h=2 target.

The h=1 exceptional case j=6 is also excluded directly: its equation `2^7=9*2^a+3a+8` has no integer a≥1, by checking a=1,2,3 and monotonicity for a≥4. This completes all hidden blocks and all source valuations.

## Reproduction and limits

The standard-library verifier enumerates the six full h=2 modular periods, checks the proposed source formulas against literal Sheep F/E, and checks the **complete** even E inverse sets for all 111 target exponents j≤1000 with j%6=0, j%18≠0. It is a finite sanity audit supporting an independently unbounded mathematical proof. The old global signed residue gap is the crucial previously established theorem for all source valuations a≥7.

**Lean arithmetic certification (2026-11-05).** The updated [PowerGatePeriods.lean](PowerGatePeriods.lean) has now been compiled locally using Lean 4.36.0-rc2 with six additional all-exponent theorems `pow45_ne44`, `pow81_eq17`, `pow153_ne35`, `pow297_ne53`, `pow585_ne71`, `pow1161_ne89`, corresponding exactly to the table. They prove the low-valuation modular rows for **all** natural exponents, rather than merely finite test cases, via period reductions and exhaustive `Fin` checks internal to the kernel. `#print axioms` for each prints only `[propext, Quot.sound]` and no `sorryAx`. The earlier full E inverse audit on 111 exponent cases is now included directly in the executable [power_h2_verify.py](power_h2_verify.py). Remaining Lean integration: exceptional h=2 and a>=7 signed-power obstruction, the source E step constructors, and the unconditional full-parent classification theorem. This is rigorous additional arithmetic formalization, with no source-connected complete theorem claim.

**Research significance:** this removes ambiguity about the direct power-gateway predecessor families for the entire j not divisible18 even sector. It does not establish that any surviving parent is absent from the genuine blank-10 orbit, and no original-source compiled all-parameter complete-classification theorem is claimed. A seed-sensitive ancestor obstruction remains the required breakthrough.