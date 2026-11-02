# Seven additional odd-exponent Sheep halting-target exclusions

**Agent 40, 2026-11-02. Intermediate mathematical theorem.** The complete proof is elementary and applies for all natural exponents; independent finite simulations and a kernel-checked Lean 4.36.0-rc2 certificate support the modular steps. The overall Sheep Machine and BB(6) remain unsolved. Prior art on the first two inverse layers: `im-results/agent15-sheep-backwards/` and `im-results/agent16-sheep-power-preimages/`.

## Statement

For the Sheep return map F defined in `README.md`, started at actual blank-tape section t=5, let
`R_odd={11,31,71,91,131,191,211}`.

**Theorem.** For every j with `j mod 300 ∈ R_odd`, set

`p_j=2(2^(j+1)−1)/5`, `x_j=(2^(j+4)−18)/25`.

The exact inverse fibers on all t≥3 are

`F⁻¹(2^j)={p_j}`, `F⁻¹(p_j)={x_j}`, `F⁻¹(x_j)=∅`.

In particular no `2^j` in these seven infinite classes is ever reached by the actual section orbit from t=5. The new exponent density 7/300 is disjoint from the prior 157/360 classes and from the five even classes `R mod 216` proved in the main README. The **combined excluded target-exponent density** is

`157/360 + 5/216 + 7/300 = 1303/2700 ≈ 48.259259%`.

This does not imply any machine-wide nonhalting theorem.

## Full proof

As in the main README, write t=2^a u with u odd. The generic branch u≥5 satisfies
`2F(t)=(2^(a+1)+1)u+2a−1`.
The universal residue-gap lemma states that for M=2^(a+1)+1, no power of two has residue D modulo M when D is odd and `1<D<2^a`. Proof: `2^(a+1)≡−1 (mod M)`, so all power residues have representatives `±2^r` for 0≤r≤a; the positive residues are 1 or even and negative representatives exceed 2^a.

Every j in the seven classes is at least 11, odd, congruent to 3 modulo 4, congruent to 11 modulo 20, and congruent to either 11 or 31 modulo 60. We use these facts below.

**The exceptional odd-part u=3 cannot contribute any incoming edges.** Its image is `f(a)=3·2^a+a+3`, strictly increasing with a. It never equals a power of two (values 6,10,17 at a≤2 and the interval `2^(a+1)<f(a)<2^(a+2)` for a≥3). For p_j, the inequalities
`f(j−2)<p_j<3·2^(j−1)`
hold because `p_j−f(j−2)=2^j/20−j−7/5>0` for j≥11. For x_j,
`f(j−3)<x_j<3·2^(j−2)`
holds because `x_j−f(j−3)=(53/200)2^j−j−18/25>0` for j≥11. Each left difference is positive at j=11 and strictly increases thereafter. The upper bounds follow immediately from the displayed formulas. Monotonicity of f rules out equality for any a. The u=1 branch has no image at all.

**Fiber 1.** Solving `F(2^a u)=2^j` on u≥5 gives
`2^(j+1)=(2^(a+1)+1)u+2a−1`.
For a≥2, the required residue `2a−1` is odd in (1,2^a), so the gap lemma eliminates all these valuations. For a=0 the equation needs `2^(j+1)≡−1 (mod 3)`, impossible because j+1 is even. For a=1 the unique source is `p_j=2u` with `u=(2^(j+1)−1)/5`. Its quotient is odd and ≥5 because j≡3 mod4 and j≥11. Direct substitution shows F(p_j)=2^j.

**Fiber 2.** With target p_j, the generic equation rearranges to
`2^(j+3)+1−10a=5(2^(a+1)+1)u`. (2)
For a≥7 the odd required residue D=10a−1 is in (1,2^a): 69<128 at a=7, and induction preserves the bound. Thus all a≥7 are impossible. For 0≤a≤6:

| a | contradiction or surviving source |
|---|---|
| 0 | Mod 3: D=−1≡2 while `2^(j+3)≡1`, since j+3 is even |
| 1 | Survives: modulo 25, `2^(j+3)≡9`; gives `u=(2^(j+3)−9)/25` |
| 2 | Mod 9: D=19≡1; actual power is 4 or 7 because j mod60=11 or31 |
| 3 | Mod 17: D=29≡12, but no power of 2 has residue 12 mod17 |
| 4 | Mod 3: D=39≡0, impossible for any power of two |
| 5 | Mod 25: D=49≡24; actual power residue is 9 |
| 6 | Mod 3: D=59≡2; the even exponent j+3 yields residue 1 |

At a=1 the integer u is odd (odd numerator divided by odd 25), at least 5, and its source `2u=x_j`. It really maps to p_j, proving the unique second inverse fiber.

**Fiber 3.** With target x_j, the generic equation becomes
`2^(j+5)−(50a+11)=25(2^(a+1)+1)u`. (3)
For a≥9, D=50a+11 is odd with `1<D<2^a`; base case 461<512 at a=9, and incrementing a adds 50 while 2^a doubles. The universal gap therefore eliminates a≥9. For 0≤a≤8:

| a | decisive modular obstruction |
|---|---|
| 0 | Mod 3: required D=11≡2, whereas j+5 even gives power residue 1 |
| 1 | Mod 125: required D=61, but actual powers are in {36,111,11,86} |
| 2 | Mod 3: D=111≡0 cannot equal a power of 2 |
| 3 | Mod 17: D=161≡8; even powers modulo 17 are {1,4,16,13} |
| 4 | Mod 11: D=211≡2; even powers modulo 11 are {1,3,4,5,9} |
| 5 | Mod 1625: D=261; actual powers for j in the seven listed residues are {536,1236,1511,586,861,211,911} |
| 6 | Mod 3: D=311≡2; even powers give 1 |
| 7 | Mod 257: D=361≡104; `2^8≡−1` mod257, so residues are `±2^r` for 0≤r≤7, none 104 |
| 8 | Mod 3: D=411≡0; impossible |

For a=1 the seven actual modulo-125 values listed in R_odd order are `36,111,11,86,111,86,36`, none61. For a=5 the seven modulo-1625 values appear in table order. Both tables apply for arbitrarily large j because `2^300≡1` modulo 125 and 1625. Their full all-exponent certificates, together with the even-power modulo 3, 11, 17 exclusions and the uniform modulo-257 lemma, have been checked by Lean 4.36.0-rc2 in `OddResidueCert.lean` with only `propext`, `Quot.sound`, and no sorryAx.

Every possible valuation in (3) is excluded, and the exceptional branch was excluded above. Hence `F⁻¹(x_j)=∅`. Since x_j>5, it is not the actual initial section state; no forward orbit from 5 can ever reach x_j without a predecessor. Consequently p_j and 2^j are unreachable as well. QED.

## Reproduction and remaining questions

- `OddResidueCert.lean`: machine-checkable, general-in-q modular certificates; it does **not** by itself formalize the full inverse theorem, large-a gap or machine-to-section bridge.
- `verify_odd.py`: exhaustive inverse enumeration confirms all three fibers for 35 target exponents up to j=1500, plus 700 modular instances. This is bounded testing independent from the proof.
- The high-value remaining question is exclusion of **all** power-of-two targets from t=5, not additional finite forward scans. The reverse sieve is one potentially automatable route; the remaining index families may have arbitrarily deep inverse trees.
