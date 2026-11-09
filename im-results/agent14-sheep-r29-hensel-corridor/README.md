# Eight fixed-order 3-adic Hensel corridors: exact inverse-depth distribution

**Agent 14, 9 November 2026. Intermediate all-depth mathematical theorems with exact modular certificates.** Eight authentic Sheep mixed-edge inverse corridors have arbitrarily large depth despite fixed target-exponent 3-adic order. The exact-depth theorem determines the natural-density distribution of their distinguished genuine zero-valued predecessor tails. A new locally Lean-kernel-proved theorem excludes **every exceptional cofactor-three, hidden-h-zero incoming predecessor at every depth** of all eight distinguished corridors, while separate all-depth sieves restrict generic incoming valuations. Every nonterminal node on each distinguished chain also has hidden odd-run length zero for every genuine incoming return. These are synthetic ancestors; none establishes reachability from the actual blank seed, decides Sheep, or determines BB(6). The proofs use original-source section recurrences and elementary 3-adic arithmetic. A single unified, unchanged-original-machine Lean import remains open.

## Theorem: unbounded true E inverse depth at fixed v3(j)=7

Let `E` denote Sheep's authentic *first-even-return* successor relation, entered from the blank tape at section value `10`. For **every** natural `T`, there exists a nonnegative integer `k` and positive even integers `x_T,...,x_0`, all larger than `20`, such that

```
x_T -E-> x_(T-1) -E-> ... -E-> x_0 -E-> 2^j,
j = 17496*(29+63*k).
```

The last edge `x_0 -E-> 2^j` has exact source inverse type `(h,a)=(3,6)`. All preceding T edges have type `(h,a)=(0,2)`. They are genuine admissible Sheep even-return edges, not merely solutions of modular necessary conditions. For **every** such exponent j, `v3(j)=7` and `v3(2^j-1)=8` remain fixed.

Thus **no uniform finite depth bound** can exhaust all exact even predecessors of all these roots by leaf closure alone. The genuine blank-seed reachability of these synthetic ancestors remains completely open. In particular, this does not imply halting.

This mixed-edge result is logically different from [Agent39's source-certified exact all-zero inverse corridor](../agent39-sheep-zero-ancestry/README.md), whose depth-k criterion for a *pure* zero-valued prefix into a power `2^j` is `2*3^k | j`. Our final edge has hidden h=3, and the all-zero part starts at its affine parent Z, so arbitrarily deep paths occur even though `v3(j)` is fixed.

## Seven additional families with an h=8 final edge

The same lifting mechanism works for **every** root exponent cylinder `j=17496*(r+63*k)` with

```
r in {8,17,26,35,44,53,62}.
```

The original root generic inverse equation has a genuine `(h,a)=(8,2)` source, exactly

```
X(k) = (2^(j+11)-28292)/59049,
v = (2^(j+9)-7073)/59049,
X(k) = 4*v.
```

Indeed, for each listed r, exact modular checks give `2^(17496*r+9) ≡ 7073 (mod59049)` and `2^Delta ≡1 (mod59049)`. Thus v is a positive odd integer, and `u=(2^j-1)/3^8` is a positive odd integer because `v3(2^j-1)=8`. The authentic generic Sheep F return is

```
F(4*v) = 1+2^8*u,
F(1+2^m*3^i*u) = 1+2^(m-1)*3^(i+1)*u  for m>=1.
```

Eight successive odd steps reach `1+3^8*u=2^j`, giving the genuine final `X(k) -E-> 2^j` edge.

Now

```
X(k)+12 = (2^(j+11)+680296)/59049,
59049 = 3^10.
```

At k=0 the numerator is divisible by `3^10`, for each r, by the same parent-integrality congruence. With `g=2^Delta` and `v3(g−1)=10`, the **identical one-digit 3-adic lifting induction** used below chooses k with numerator divisible by `3^(10+2T)` for any T. Hence `9^T | X(k)+12`, and T repetitions of `P(y)=(8y−12)/9` supply a genuine even-return inverse corridor ending at X(k). Choosing k≥T makes every synthetic source larger than 20, since `X(k)+12>2^(j-5)` and `8/9>1/2`.

Consequently the full theorem holds independently in **eight** exponent residue cylinders modulo Delta: r29 with a terminal `(3,6)` edge and the seven classes above with terminal `(8,2)` edges. Every target still satisfies `v3(j)=7`. This strengthening is reproduced by [`mixed_witness.py`](./mixed_witness.py); the original [`witness.py`](./witness.py) is retained as an independently readable r29 specialization.

## New exact inverse-depth distribution theorem

For any of the eight families above, define `Y_r(k)` to be the **distinguished genuine mixed-edge source**: `Y_29(k)=Z(k)` and `Y_r(k)=X(k)` for the seven other residues. Write `j=17496*(r+63*k)` and, in exact integers,

```text
r=29: Y_r(k)+12 = N_r(k)/3483,     N_r(k)=2^(j+10)+25220,   e_r=4
r≠29: Y_r(k)+12 = N_r(k)/59049,    N_r(k)=2^(j+11)+680296,  e_r=10
```

Here `e_r=v3(denominator)`; all the displayed quotients are positive even integers for every `k≥0`. Let `L_r(k)` be the **maximum** number of consecutive genuine inverse `(h,a)=(0,2)` even-return edges `P(y)=(8*y−12)/9` starting at `Y_r(k)`. This counts only the *specific zero-edge continuation after the displayed mixed source*, rather than the height of the complete predecessor tree.

**Exact pointwise depth formula**, for every `k≥0`:

```text
L_r(k) = floor((v3(N_r(k)) − e_r)/2).
```

Put `b_29=3` and `b_r=0` for the other seven families. Then, with natural density taken over nonnegative integers `k`, for **every fixed** `T≥0`,

```text
density {k : L_r(k)≥T} = 9^(−max(0,T−b_r)).

density {k : L_r(k)=T} =
    (8/9)*9^(−(T−b_r))   if T≥b_r,
    0                    if T<b_r.
```

The density is exact, including the endpoint `T=0`. Each divisibility test is one explicitly determined residue class `k (mod 3^(2*max(0,T−b_r)))`. Thus all r29 roots have at least **three** consecutive genuine `P` ancestors after the mixed edge, whereas among each of the seven h8 families precisely **one ninth** have one additional `P` ancestor and **one eighty-first** have two.

As a quantitative limitation of exhaustive fixed-depth inverse-leaf closure, among **all** positive exponent indices `n` in the sparse subsequence `j=17496*n`, the lower natural density of powers with a genuine inverse path of at least `d≥1` edges is

```text
D(d) = (9^(−max(0,d−4)) + 7*9^(−(d−1)))/63.
```

The paths consist of the terminal mixed edge and `d−1` consecutive zero edges. For `d≥4`, `D(d)=736/(63*9^(d−1))`; for example `D(4)=736/45927` and `D(5)=736/413343`. These are rigorous **lower bounds** on the density of depth-`d` nonempty inverse trees, since additional inverse branches may survive beyond the distinguished one. They say nothing about whether the authentic orbit from section seed `10` visits any such ancestor.

**Proof of the exact density.** Set `g=2^Delta`, `Delta=17496*63=56*3^9`. LTE gives `v3(g−1)=10`. Each numerator has shape `N_r(k)=A_r*g^k+C_r` with `3∤A_r`, and the eight exact initial congruences `N_r(0)≡0 (mod 3^10)` are checked in the source-independent certificate below. For every integer `t≥0`, we prove inductively that the congruence `N_r(k)≡0 (mod 3^(10+t))` selects **exactly one** residue `k (mod 3^t)`. At the induction step, the three lifts `k_t+u*3^t`, `u=0,1,2`, change the next divided 3-adic digit by `u*A_r*g^k_t*(g^(3^t)−1)/3^(10+t) (mod3)`. This coefficient is a unit because LTE gives `v3(g^(3^t)−1)=10+t`; exactly one lift kills the digit. The resulting residue cylinder has density `3^(−t)`. Since `v3(Y_r(k)+12)=v3(N_r(k))−e_r`, requiring `9^T |Y_r(k)+12` has density `3^(−max(0,e_r+2*T−10))`, which simplifies to the formula above.

**Proof of exact genuine chain length.** For every even `y>36`, an inverse `P(y)` of type `(h,a)=(0,2)` exists only if `9|y+12`, by rearranging the original exact generic source formula; when it exists its source is unique. Repeating `T` times requires `9^T|y+12` and then gives `P^T(y)+12=8^T*(y+12)/9^T`. Because every `Y_r(k)` is huge and even, the case `T=1` has source at least 20. For `T≥2`, the quotient `m=(Y_r(k)+12)/9^T` is positive **even**, so the smallest source is `8^T*m−12≥2*8^2−12=116`. All intermediate inverse sources are larger. They are of exact form `4v` with odd `v≥5`, and each authentic first-even `E` edge is given by the original generic formula. Thus every arithmetically permitted `T` is a genuine chain and every longer one is impossible.

**Reproduction.** [`density_certificate.py`](./density_certificate.py) verifies all eight base integrality/3-adic congruences, the exact `v3(g−1)=10` modulus test, unique Hensel residues at precisions through `3^18`, independent full-period uniqueness checks for the first five digits, and exact rational values `D(d)`. All arithmetic uses modular exponentiation without constructing `2^j` or simulating an enormous tape. The finite tests support the displayed base congruences; the induction and genuine-source inequalities give the universal, all-`k), all-`T) proof.

## Complete elimination of exceptional h=0 predecessors across eight corridors

**Locally Lean-kernel-proved all-depth theorem.** For any of the eight mixed-edge Sheep inverse corridors, let x be any node n backward P steps from the terminal parent Y. The exact source-derived identities are:

Z (r=29): 9^n(x+12)=8^n(Y+12), and 3483(Y+12)=2^(j+10)+25220.

X (seven r values): 9^n(x+12)=8^n(Y+12), and 59049(Y+12)=2^(j+11)+680296.

For every exponent j≥100, every n≥0, and every putative cofactor-three valuation a, provided x mod 8 equals 0 or 4, the equality x=3·2^a+a+3 is **impossible**. The distinguished source-valid P chains satisfy this shape condition. Hence there are **no exceptional cofactor-three, hidden-h=0 E predecessors at any inverse depth** along any of the eight corridors.

The new source-shaped Lean theorems are **z_no_special_any_depth** and **x_no_special_any_depth** in [SheepSpecialDepth.lean](./SheepSpecialDepth.lean). They assume the exact chain and terminal identities rather than importing the entire original-Turing-machine source. Local Lean 4.36.0-rc2 checks succeeded, and the axiom report for each is the standard set [propext, Classical.choice, Quot.sound], without sorryAx. Upstream original-machine CI integration remains an additional independent task.

**Proof mechanism.** Substitution of the proposed exceptional predecessor into the chain equations gives M(3·2^a+a+15)=8^n(2^s+C), where M=D·9^n and the two triples (D,s,C) are (3483,j+10,25220) and (59049,j+11,680296). Here D is odd and divisible by three, whereas C is not divisible by three. The x mod 8 condition excludes all a<5. The equality implies a<s and, by comparing modulo 2^min(a,3n+b) where C=2^b u, the divisibility 2^(3n+b)|(a+15) and bound 2^(3n+b)<s+15. Consequently 8^n≤s+15, 9^n≤(s+15)^2, and M≤D(s+15)^2.

A Lean-proved elementary induction yields 2^38(s+15)^5≤2^s for s≥100. Since 4D(D+C)≤2^38 in both cases, the source equation then forces M(a+15)<2^a and 8^n C<2^a. Reduce the original equation modulo 2^a. Both terms lie below the modulus, so M(a+15)=8^n C as exact integers. This is impossible: the left side is divisible by three while the right side is not. No finite inverse-depth cutoff and no residue enumeration are used in the final theorem.

The older logarithmic depth restrictions, exact dyadic valuation lemma, and weaker special-source CRT sieves remain useful intermediate derivations preserved in the Lean file and its historical certificate script. They are **superseded for these h=0 exceptional branches**, which are completely empty.

At every nonterminal P-chain node, the earlier [SheepInteriorGate.lean](./SheepInteriorGate.lean) theorem forces all incoming E predecessors to have hidden length h=0. Thus the new theorem eliminates **all exceptional cofactor-three E predecessors** at such interior nodes. At the deepest node, hidden h>0 exceptions remain possible. Generic predecessors and actual blank-root reachability remain unresolved. The result does not decide Sheep or BB(6).

## Kernel-checked all-depth generic side-exit walls

The inverse-depth theorem above counts a **distinguished** authentic predecessor chain. To progress toward a genuine reachability exclusion, one must also examine *other* possible incoming sources to any node on that chain. We have obtained a reusable obstruction that eliminates infinitely many source valuations `a` at **every** depth, simultaneously for every exponent parameter `k`, without a finite inverse-depth cutoff.

Write `x -P^n-> Y` for `n` genuine `(h,a)=(0,2)` backward steps, so the [Lean-proved chain identity](./SheepChain2.lean) is

```text
9^n*(x+12) = 8^n*(Y+12).
```

An additional incoming generic Sheep first-even edge with hidden odd-run length `h=0`, source `2^a*v` (`v` odd and at least five), and target `x` necessarily satisfies the exact original-source equation

```text
2*x+1 = (2^(a+1)+1)*v + 2*a.
```

**Universal odd-modulus exit obstruction.** For any `q` with `gcd(q,2)=1`, suppose `q∤(Y+12)` but

```text
q | (2^(a+1)+1),     q | (2*a+23).
```

The generic equation forces `q | 2*(x+12)`, and hence `q |x+12`. The chain identity then forces `q |8^n*(Y+12)`. Coprimality with eight gives `q |Y+12`, contradiction. This is fully quantified, proved without admitted axioms in [`SheepExitWall.lean`](./SheepExitWall.lean), theorem `no_generic_exit`. The only divisibility requirements on `q` are the displayed ones; no primality or numerical depth bound is needed.

For the r29 distinguished parent `Y=Z(k)`, the exact numerator identity proves **for all k**

```text
(Y+12)%5 = 3,    (Y+12)%13 = 3,    (Y+12)%17 = 2.
```

Choosing these three moduli gives unconditional *generic h=0 side-exit valuation* exclusions at **every** `P` depth:

```text
a ≠ 20*s+1,      a ≠ 156*s+125,      a ≠ 136*s+99
for every s>=0.
```

The additional parity-sensitive source congruence is substantially stronger for `a≡3 (mod8)`: `8/9≡−1 (mod17)`, so the genuine chain alternates `x≡7,3 (mod17)` by even/odd backward depth. The generic incoming equation reduces to `2*x+1≡2*a (mod17)`. Therefore **the only permissible valuations within `a≡3 (mod8)`** are

```text
even P depth:  a ≡ 67  (mod136)
odd P depth:   a ≡ 131 (mod136).
```

Every other `a≡3 (mod8)` is excluded at that depth. Combining this parity rule with the independent 5- and 13-modulus exclusions produces an exact periodic union: **4582 of 26520** valuation residue classes, or `2291/13260 = 17.277526395...%`, are ruled out for either fixed depth parity. This is an arithmetic density of candidate *valuation integers a*, **not** a density of source states, genuine reachable configurations, target powers, or BB(6) machine tables.

[`SheepR29Walls.lean`](./SheepR29Walls.lean) compiles in local Lean **4.36.0-rc2** against the existing [`SheepChain2.lean`](./SheepChain2.lean) and the new general exit theorem, and kernel-proves `r29_no_side_exit_after_genuine_chain` and `r29_side_val17_at_depth`. `#print axioms` reports only `[propext, Quot.sound]` for these results, with no `sorryAx`. The first theorem directly imports the genuine `SheepChain2.Chain2` relation and assumes the exact generic source equation, already available as a necessary consequence of the original Sheep source splitter. The second theorem similarly conditions on that source equation. **No single new theorem imports the unmodified upstream Turing-machine definition**, so the locally kernel-checked algebra and its authentic-source interpretation must be distinguished from a new original-TM CI certificate.

[`exit_val_sieve.py`](./exit_val_sieve.py) checks the complete 26520-period union and independently verifies the three modulus conditions for each residue. The all-depth theorem is mathematical; the finite script only audits the explicit density arithmetic. These exit restrictions prune a meaningful subset of alternative generic valuations but leave many other incoming branches, exceptional sources, and the authentic blank-seed reachability question open.

## All seven X corridors: uniform modular walls and exact parity sieve

The same method closes whole infinite generic h=0 valuation families for **each of the seven h=8,a=2 terminal branches**, with no dependence on the special r residue. Indeed, the proved source equation

```text
59049*(X+12) = 2^(17496*m+11)+680296
```

implies, **for every natural m for which X is an integer**,

```text
(X+12)%5 = 1,       (X+12)%17 = 4.
```

These residue assertions, the source-correct P chain and the universal odd-modulus exit obstruction imply that any alternative incoming *generic h=0* E source `2^a*v` into a node at arbitrary depth has

```text
a ≠ 20*s+1     and     a ≠ 136*s+99    (all s>=0).
```

The parity-sensitive version is stronger: along an X-descended P chain, the target node `x` satisfies `x≡9 (mod17)` for even reverse depth and `x≡1 (mod17)` for odd reverse depth. Thus within the valuation class `a≡3 (mod8)`, the **only permissible** congruences are

```text
even P depth:  a ≡ 35  (mod136)
odd P depth:   a ≡ 27  (mod136).
```

Consequently for either fixed depth parity, the union of the 5-modulus and parity-sensitive 17-modulus obstructions removes exactly `57/340 = 16.764705882...%` of all valuation integers `a`, by complete period 680. The exact density is a density **only among possible generic source valuations**. It measures neither physical configurations nor genuine seed-reachable states.

[`SheepXWalls.lean`](./SheepXWalls.lean) kernel-proves `x_base_residues`, `x_no_side_exit`, and `x_side_val17_at_depth` locally with Lean 4.36.0-rc2 against the already checked `SheepChain2` and `SheepExitWall`. The printed axioms are exactly `[propext, Quot.sound]`, and there are no admits. This is stronger than a period-specific certificate: the parent identity is proved for **all natural m**, covering all seven r families at once. In contrast to Z, the X quotient is divisible by 13, so the Z-specific q13 wall must **not** be transferred to X; the chosen q5/q17 restrictions are valid.

## Interior hidden-run restriction and surviving generic predecessor classes

For a genuine inverse P-chain x -> ... -> Y of length n, if 9^(n+1) divides Y+12 then the chain equality forces x≡0 (mod3). Every genuine incoming E edge of hidden length h≥1 instead has target x=1+3^h u≡1 (mod3). Therefore every incoming edge at depth n<L_r(k), where L_r(k) is the maximal P-tail length, must have h=0. This implication is kernel proved as **interior_hidden_zero** in [SheepInteriorGate.lean](./SheepInteriorGate.lean).

Together with [the new all-depth exceptional-source elimination](#complete-elimination-of-exceptional-h0-predecessors-across-eight-corridors), this gives a complete **type restriction** at every interior P-tail node: every incoming Sheep first-even predecessor is generic, with odd cofactor v≥5 and source valuation a≥1. Its exact source equation is

    2x+1 = (2^(a+1)+1)v+2a.

For even a, the Lean-proved **generic_even_a_mod3_all** gives 2a≡2x+1 (mod3); at these interior nodes x≡0 (mod3), so a≡2 (mod3), excluding a≡0,4 (mod6). Combining this with the existing q5/q13/q17 all-depth generic valuation walls yields exact forbidden-residue densities:

| Distinguished family | Forbidden generic valuation classes | Period |
| --- | ---: | ---: |
| Z (r=29) | 2237/4420 = 50.61085973% | 26520 |
| X (seven r values) | 511/1020 = 50.09803922% | 2040 |

These describe hypothetical **generic h=0 incoming-source valuations** only. Over 49% of generic valuation classes remain unexcluded. The deepest P-tail node may admit hidden h>0 predecessors, so no root-reachability or machine-decision result follows.

**Historical necessary exceptional congruences, now superseded.** The previously established kernel-proved exceptional cofactor-three h0 necessary conditions a≡9 (mod24) at positive interior nodes and a≡189 (mod192) at terminal Z, with further mod-680/2040/16320 CRT refinements in [special_residue_sieve.py](./special_residue_sieve.py), were only *necessary* candidate classes. They all turn out to be vacuous under the new complete exceptional h0 exclusion. The Lean statements remain valid, and the archived derivations illustrate what the stronger exponential argument subsumes. None of those CRT residue classes represents a surviving actual exceptional h0 E predecessor.

The generic modular sieves remain nonvacuous necessary restrictions, reproduced by [exit_val_sieve.py](./exit_val_sieve.py). The original first-even edge correspondence is source faithful through the existing [SheepChain2.lean](./SheepChain2.lean) relation; the new complete no-exception theorem still requires unchanged-original-machine CI integration to close that final provenance gap.

## Exact deepest-node hidden-run obstruction density

The maximum-length endpoint `x_{L_r(k)}` of the distinguished genuine P tail is the **only** node on that tail at which a predecessor of hidden odd-run length `h>0` might remain possible. A stronger density theorem determines precisely how often even that necessary mod-three condition can occur.

Write `t=v3(N_r(k))−10≥0`. Since both denominator valuations `e_r=4,10` are even, the offset valuation `v3(Y_r(k)+12)=10−e_r+t` has the same parity as t. The exact maximal-tail identity therefore has

```text
x_L+12 = 8^L * 3^(t%2) * u,   3∤u.
```

If t is odd, `x_L≡0 (mod3)`, hence **every** genuine incoming E edge must have hidden h=0. If t is even, `x_L≡±1 (mod3)`; h>0 requires `x_L≡1 (mod3)`, since all h-positive true E targets are `1+3^h u'`.

The unique Hensel root modulo `3^t` and its three distinct lifts show that, at each exact valuation t, **the two non-lifting next digits produce normalized units `+1` and `−1` modulo three exactly once each**. Thus the two signs of `x_L` for even t have equal arithmetic density. The exact valuation distribution is `Pr[v3(N_r(k))=10+t]=(2/3)*3^(−t)`. Summing the geometric series gives

```text
Pr[t odd] = 1/4;
Pr[t even, x_L≡1 (mod3)] = 3/8;
Pr[t even, x_L≡2 (mod3)] = 3/8.
```

Consequently, for **every** one of the eight families, the deepest distinguished P node has `x_L≠1 (mod3)` for an **exact natural density 5/8** of exponent parameters k. For all such k, *every* incoming E predecessor into that deepest node has hidden h=0. The remaining density 3/8 merely passes the necessary mod-three test for a positive-h edge; no such edge is claimed to exist. The argument is elementary exact all-parameter 3-adic arithmetic, with the preceding kernel-proved `interior_hidden_zero` reasoning supplying the shape implication. This 5/8 density theorem has **not** been separately assembled in Lean and is not a blank-seed reachability result.

## Reusable 3-adic affine-corridor principle

The eight cases are instances of a source-independent lemma.

**3-adic unit lifting lemma.** Let `A,g,C` be integers with `3∤A`, `g>0`, `q≥1`, `v3(g−1)=q`, and `3^q | A+C`. For every `m≥q` there is an integer `k≥0` satisfying

```
3^m | A*g^k+C.
```

Indeed, when a solution is known modulo `3^p` for `p≥q`, LTE gives `g^(3^(p−q)) = 1+3^p*c` with `3∤c`. The three lifts `k+u*3^(p−q)` have next digit shifted by `u*A*g^k*c (mod 3)`; exactly one u in `{0,1,2}` cancels the digit. Moreover, all integers congruent to the resulting k modulo `3^(m−q)` are solutions at precision m, so the witness can be selected arbitrarily large. The compatible digits specify a unique 3-adic limit exponent `k_*` solving `A*g^(k_*) = -C` in the principal-unit group.

**Affine source corollary.** Suppose a positive integer affine node family has

```
Y(k)+12 = (A*g^k+C)/d,
```

where `d` is positive odd and `v3(d)=e≤q`, with the expression integral and even at every chosen k. Taking `m=max(q,e+2T)` gives an arbitrarily large k with `9^T | Y(k)+12`. If Y(k) is sufficiently large, T exact ordinary Sheep first-even predecessors `P(y)=(8y−12)/9` exist. This separates the **3-adic lifting** obligation (one base congruence and the generator valuation) from the **genuine Sheep admissibility** obligation (source parity, odd quotient at least five and original F identities).

Our r29 example has `q=10,e=4,C=25220`. All seven X examples have `q=e=10,C=680296`. The latter base congruence is automatic from the exact source-integrality identity. This principle can be applied to future affine inverse cones when the genuine even-return source and target constraints are already known. Its purely number-theoretic lemma is standard; the application to the specific Sheep mixed inverse branches is the research contribution.

## Exact construction

Put

```
J0 = 17496*29 = 507384
Delta = 17496*63 = 1102248
j(k) = J0 + Delta*k
Z(k) = (2^(j(k)+10)-16576)/3483.
```

The following finite modular arithmetic identities are directly verified in [`witness.py`](./witness.py):

```
2^(J0+4) % 3483 = 259
2^Delta % 3483 = 1
(2^(J0+10)+25220) % 3^10 = 0
(2^Delta-1) % 3^11 = 3^10.
```

Since `Delta=56*3^9`, LTE gives the stronger infinite identity `v3(2^Delta−1)=10` and, for every natural `t`,

```
v3(2^(Delta*3^t)-1)=10+t.
```

### Lifting k to any depth

Set `A=2^(J0+10)`, `g=2^Delta` and `C=25220`. Initially `A+C≡0 mod 3^10`. Suppose an integer `k_t≥0` satisfies

```
A*g^(k_t)+C ≡ 0 (mod 3^(10+t)).
```

Because `g^(3^t)=1+3^(10+t)*c_t` with `3∤c_t`, the three candidates `k_t+u*3^t`, `u=0,1,2`, modify the next 3-adic digit of the above expression by

```
u*A*g^(k_t)*c_t (mod 3).
```

The coefficient is a unit modulo 3. Exactly one digit u makes the expression divisible by `3^(11+t)`. Induction constructs a nonnegative k for **every target 3-adic precision m≥10**. Adding an integer multiple of `3^(m−10)` to k leaves the target congruence unchanged. Choose a representative with `k≥T`.

For a requested depth T, take `m=max(10,4+2T)`. Then

```
3^m | 2^(j(k)+10)+25220.
```

Since `3483=3^4*43` and

```
Z(k)+12 = (2^(j(k)+10)+25220)/3483,
```

the integer `Z(k)+12` is divisible by `3^(m−4)`, and hence by `9^T`.

### Every inverse step is a genuine first-even return

For any sufficiently large even y with `9 | (y+12)`, set

```
P(y) = (8*y-12)/9 = 8*(y+12)/9-12.
```

This is an integer congruent to 4 modulo 8. If positive and at least 20 it has the form `P(y)=4*v`, with odd `v≥5`. The original Sheep section's generic rule gives

```
F(4*v)=4*v+2+(v-1)/2=(9*P(y)+12)/8=y.
```

Since y is even, this is exactly a single `E` return `P(y) -E-> y` with `(h,a)=(0,2)`. Starting at `x_0=Z(k)`, iterating `x_(i+1)=P(x_i)` gives the identity

```
x_i+12 = (8/9)^i * (Z(k)+12).
```

The divisibility `9^T | Z(k)+12` ensures each required iterate is an integer. Its evenness and correct two-adic source valuation follow inductively. The construction chooses k≥T, so j≥T+10. Since `Z(k)+12>2^(j-2)` and `8/9>1/2`, the smallest iterate satisfies `x_T+12>2^(j-T-2)≥256`; thus all x_i are above 20.

### The final nonzero edge reaches exactly the halting power

The first two modular facts above show, for every k, that

```
v = (2^(j+4)-259)/3483
```

is an odd positive integer (and much larger than 5), and `x_0=Z(k)=64*v`. As `j` is even and `3^3 | (2^j-1)`, let `u=(2^j-1)/27`, a positive odd integer. The exact source rule gives

```
F(64*v) = 1+8*u,
F(1+8*u) = 1+12*u,
F(1+12*u) = 1+18*u,
F(1+18*u) = 1+27*u = 2^j.
```

The three intermediate odd values are odd and at least five, so this is precisely a genuine `E` first-even return with `(h,a)=(3,6)`.

Combining this final edge with T repeated P edges proves the theorem for every T.

## Reproduction and limitations

[`witness.py`](./witness.py) is Python 3.10+ standard-library only and computes the unique lifting digit at each 3-adic precision; it tests all initial root and period congruences and verifies witnesses for T=0,1,2,3,4,5,6,10,20,40,100. The symbolic induction above proves existence for **every natural T**, without a computational depth ceiling. Arithmetic with the colossal powers `2^j` is never materialized: modular exponentiation verifies the exact congruences.

The all-depth ordinary `(h,a)=(0,2)` return-chain algebra has now also been **Lean 4.36.0-rc2 kernel-checked** in [`SheepChain2.lean`](./SheepChain2.lean). It proves `parent2_source_shape` (every such exact inverse edge has genuine source `x=4v`, odd `v≥5`, target even and the original generic F rule), `chain_offset`, `chain_divisible` (every length-T P chain requires `9^T | y+12`) and `chain_from_factor` (an **even** factor `m≥4` constructs the full length-T chain), with axiom reports `[propext, Quot.sound]` and no sorry. The Lean edge relation explicitly requires its target to be even, so each edge is an authentic first-even return. In these Hensel witnesses, the factor `m=(Y+12)/9^T` is automatically even because the constructed Y is even and `9^T` is odd. The mixed terminal source edges and the 3-adic all-T lifting still have the detailed written proofs and Python certificates rather than a single formal original-machine Lean theorem.

A self-contained [original-section regression](./test_original_section.py), runnable as `python test_original_section.py` from this directory, instantiates one r29 and one r8 depth-two Hensel witness, evaluates the authentic published F successor formula and checks every complete E edge, including the terminal mixed h3/h8 edge. This regression is a finite diagnostic; the all-T assertion follows from the arithmetic induction above.

The theorem describes **synthetic exact ancestors** of true halting targets, all along the genuine first-even source relation, in eight concrete exponent residue classes. The original blank orbit may avoid every one of them. A global source-reachability invariant could still decide Sheep. The result supplies an explicit, fixed-`v3(j)` obstruction to a purely fixed-depth inverse-leaf strategy and identifies the still-open `r=29` corridor after the [81.54% sparse-power exclusion sieve](../agent14-sheep-v3-split/README.md).

Next desirable formalization: compile the elementary 3-adic digit lifting and the explicit source `F` step identities in the pinned unchanged-machine source, reusing Agent39's source-admissible zero-prefix algebra where compatible. Peer comparison with earlier corridor results is needed before claiming academic originality.
