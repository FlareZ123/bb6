# Seven additional periodic Sheep first-even inverse cones

**Agent 14, 2026-11-05. Intermediate mathematical result; source-aligned paper proof plus a complete integer certificate. Sheep and BB(6) remain undecided.** These seven exponent progressions were not among the nine earlier exact Sheep E families recorded in `im-results/agent14-sheep-even-inverse/ROOT-FREE-CONES.md` and `im-results/agent16-sheep-new-even-cones/README.md`. An overlap with stronger unpublished or external methods is not ruled out.

## Claim and exact source semantics

For the six-state Sheep machine
`1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`,
the original-source reduction of Agent16 proves that raw blank-tape halting is equivalent to the first-even section orbit `EvenReach 10` encountering a power `2^j`. On defined even sources `x=2^a v`, with `a>=1`, odd `v>=3`, the ordinary return is

- `F(x)=x+a+3` if `v=3`;
- `F(x)=x+a+(v-1)/2` if `v>=5`.

The first-even successor is `E(x)=1+3^h (F(x)-1)/2^h`, where `h=v_2(F(x)-1)`. These equations and the authentic initial even section 10 are from [Agent16's original-source bridge](../agent16-sheep-even-return/README.md), whose pinned-source CI [41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547) is a separate, already existing verification. The present arithmetic certificates use those exact equations.

**New all-k claim:** for each row below and all natural `k`,

```
not EvenReach(10, 2^(J + P*k)).
```

| J | P | Complete E inverse nodes | Actual inverse edges | Low-valuation pairs | Complete periodic representatives |
|---:|---:|---:|---:|---:|---:|
| 188 | 55,080 | 3 | 2 | 68 | 218 |
| 190 | 306,180 | 4 | 3 | 54 | 172 |
| 220 | 55,080 | 4 | 3 | 61 | 227 |
| 262 | 53,460 | 4 | 3 | 59 | 230 |
| 442 | 1,837,080 | 3 | 2 | 105 | 368 |
| 624 | 29,160 | 3 | 2 | 48 | 146 |
| 648 | 122,472 | 2 | 1 | 57 | 194 |
| **Total** | | **23** | **16** | **452** | **1,555** |

All seven infinite families are pairwise disjoint. Each avoids every one of the four previous Agent14 E families and five previous Agent16 E families, by exact residue compatibility checks modulo the respective gcds. The older symbolic five-generation *ordinary-section* F certificate [Agent16](../agent16-sheep-deep-sieve/README.md) excluded 3,596 residue classes modulo 5,400. The new verifier constructs a real five-edge F inverse chain at each base J, proving that its corresponding residue class cannot already be closed by that particular depth-five procedure. Restricting each progression to `j=J+lcm(P,5400)*k` therefore yields seven mutually disjoint E exclusions also disjoint from the older F-depth-five certified set.

The resulting **guaranteed additional density of forbidden halting exponents** beyond that previously stated nine-E-family/F-depth-five union is exactly

```
1/275400 + 1/3061800 + 1/275400 + 1/534600
+ 1/9185400 + 1/145800 + 1/3061800
= 4111/245381400.
```

This is a density of exponent indices, not a probability of halting, a new BB(6) bound, or a decision of the Sheep machine. It is a conservative increment: we count only one F5-disjoint refined subprogression of each new class.

## Complete symbolic inverse certificate

Each node in the table is an exact rational-exponential function
`Y(j)=(2^(j+s)+b)/d`, with odd positive `d`, even `b`, and `j=J+Pk`. The Python file [seven_cones.py](seven_cones.py) explicitly lists all 23 triples and 16 reverse edges. Its checker adapts and credits the existing Agent16 five-cone [certificate.py](../agent16-sheep-new-even-cones/certificate.py), with newly derived case data and five-step F-path witnesses. This is a **complete-period mathematical certificate**, with exact integers throughout and no cutoffs on the actual machine's running time, `k`, `a` or `h`.

Here is the proof reducing the infinite requirements to the checked integers:

1. **Finite possible 3-adic hidden length.** At each node `Y`, the program calculates `H=v_3(Y(J)-1)+1`, proves `2^P≡1 (mod d·3^H)`, and checks the base residue. Hence `v_3(Y(J+Pk)-1)=H-1` for every `k`, so any predecessor has `0<=h<H`. It also proves node integrality, separation, and `Y(J+Pk)>10` universally.

2. **Exact predecessor equations.** For a fixed node `(s,b,d)` and a possible `h`, define `D=d·3^h`, `C=2^h(b-d)+D`, and `N=j+s+h`. If the source has generic odd part `v>=5`, the exact necessity is
   ```
   2^(N+1) ≡ K(a) (mod D(2^(a+1)+1)),
   K(a) = D(2a-1) - 2C.
   ```
   For the special odd part `v=3`, the exact equation is
   ```
   3D·2^a + D(a+3) - C = 2^N.
   ```
   These follow by substituting `F(x)` into the first-even formula; no exceptional type of even incoming edge is omitted.

3. **Exclude all unbounded generic valuations.** The verifier finds a finite `A` with `1<K(A)<2^A` and `2^A>=2D`. Since `K(a+1)=K(a)+2D` and `K(a)` is odd, induction preserves `1<K(a)<2^a` for all `a>=A`. Modulo `2^(a+1)+1`, any power of two is congruent to `±2^r` for some `0<=r<=a`. No odd residue strictly between 1 and `2^a` is of that form. Hence all `a>=A` are impossible.

4. **Exclude every special predecessor.** Choose `e` with `2^e<3D<2^(e+1)` and write `g=e-(s+h)>=0`. Put `L=3D-2^e>0` and `U=2^(e+1)-3D>0`. The verifier checks
   ```
   L·2^J > 2^g C,
   U·2^J > 2^(g+1)(D(J+3)-C),
   U·2^J >= 2^(g+1)D.
   ```
   These bounds persist for all later j. With `b_0=j-g`, if `a>=b_0`, the leading `3D·2^a` exceeds `2^N` by at least `L·2^b_0`, which exceeds `C`; the positive `D(a+3)` strengthens the gap. If `a<b_0`, the leading term is below `2^N` by at least `U·2^(b_0-1)`, larger than `D(j+3)-C`. Either case contradicts the special equation.

5. **Exhaust the remaining finite valuations uniformly in k.** For each `1<=a<A`, put `m=D(2^(a+1)+1)` and calculate the exact multiplicative order `o=ord_m(2)` by modular doubling. Let `q=o/gcd(o,P)`. The `q` residues of `k` cover a complete power-congruence period. The verifier checks all 1,555 resulting exact residues. Only the declared 16 generic edge parameter pairs survive, and every one survives for the **entire** k period. Its child identity is verified symbolically; the quotient defining `v` is always an odd integer and at least five, hence is an actual edge for every k. Direct `E(x)=Y` calculations at k=0,1 independently recheck these edges.

All predecessor sets are therefore **exactly** the listed finite acyclic graph, for every k. No node equals the initial 10, and all reverse edges move to a higher numbered node. If the real even orbit from 10 reached the root, recursively taking a last predecessor would eventually force a leaf with no possible predecessor, a contradiction. This proves the seven all-k reachability exclusions in the source-defined even graph, assuming the already authenticated reduction.

## Reproduction and provenance

Run `python3 im-results/agent14-sheep-seven-cones/seven_cones.py` using Python 3.10+ (standard library only). It recomputes every modular order rather than trusting a factorization or external group-order routine. It checks 452 low-valuation conditions over 1,555 period representatives; seven E graphs, 16 actual edge constructors, 39 special-case rows, and the seven real F five-edge paths. A manual-only workflow [agent14-sheep-seven-cones.yml](../../.github/workflows/agent14-sheep-seven-cones.yml) can check the exact committed script without a per-commit CI trigger.

**Evidence boundary:** locally an independent Python implementation reproduced every listed arithmetic count, path, and complete-period congruence, and the repository script reuses Agent16's established verifier mechanics. A completed successful workflow run, if available, authenticates the committed source arithmetic. The new seven-family statements have **not** been assembled into an unchanged-source Lean kernel theorem with the genuine `SheepEven.EvenReach` induction. Their status is a complete arithmetic/paper proof connected by the established semantic reduction, pending adversarial review and Lean integration. The actual blank orbit may still encounter other powers; full Sheep nonhalting and BB(6) remain open.

**Next worthwhile task:** parameterize the existing Agent14/40 original-source Lean inverse-reachability gate over a finite list of rational-exponential nodes and import these seven all-k module certificates. More importantly, seek a genuine blank-seed forward invariant eliminating entire surviving power-gate sectors, because residue-class inverse exclusions alone cannot decide the holdout.
