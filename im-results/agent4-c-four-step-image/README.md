# Machine C: a sharp fourth-return gap and exact eventual fourth-image density

**9 November 2026, Agent 4.** Source map: `BB6.Agent46.secNext`, the unmodified original Machine C first-return section, initially `(5,1)`. Let `I_r` be the set of outputs with `r` consecutive successful source transitions from *arbitrary* source inputs. The original blank orbit is a far smaller set.

## Source-certified theorem: a strict three-versus-four image cone

For **every** pair of natural counters `(x,y)` with

```
y >= 70, (x+y) mod 8 = 1, y mod 32 = 22,
```

there are exactly **three possible consecutive incoming source transitions** in the sense that `(x,y) in I_3` and `(x,y) not in I_4`. This is an infinite two-dimensional residue cylinder, with asymptotic density **1/256** of all section coordinates. All-time genuine blank-origin nonreachability follows:

```
forall time, run secNext time (some (5,1)) != some (x,y).
```

The reason is structural. The exact complete source inverse theorem forces the **unique** immediate parent

```
P=(x+y-2,(y-2)/2).
```

Under the stated residues, `P` satisfies `P.right>=34`, `(P.left+P.right)%8=1`, and `P.right%16=10`. Agent 34 previously source-certified that these `P` have two genuine parents but no three. Their original strict `I_2 \\ I_3` theorem gives the two incoming witnesses; the genuine direct edge `P -> (x,y)` supplies a third. A fourth edge would require a third ancestor of `P`, contradiction.

This is the first **concrete all-time fourth-return blank exclusion** in the Agent 4 dossier. The new sharp residue cone is disjoint from the previously established Agent 4 strict `I_2 \\ I_3` cone, which has right residue four modulo eight.

**Unconditional high-stopping pullback.** The original source halting equation for the high family is

```
k+j+3*m+5 = 2^(2*m+2)*(j+3).
```

For **every** natural `j,m,k,time` satisfying it and

```
m>=3, j%4=0, m%4=3, (j+3*m+5)%32=10,
```

the authentic blank section never reaches `(2*j+3,k)`. There are **eight qualifying (j,m) cells modulo 32 in each coordinate**, hence this infinite exclusion occupies **1/128** of high-stopping parameter pairs. The cells, written `(j mod32,m mod32)`, are `(0,23),(4,11),(8,31),(12,19),(16,7),(20,27),(24,15),(28,3)`. This family is disjoint from Agent 4's earlier `j`-odd high stopping diagonal, but overlap with *all* independent old sieves still needs checking.

**Verification.** [Source Lean proof](CThreeToFourSource.lean), imported after `ThreeConeSource` and `CThreeArithmetic`, compiled against unchanged original source in manual [CI 42600105398](https://github.com/FlareZ123/bb6/actions/runs/42600105398) for `four_edge_impossible`, `blank_no_four_cylinder`, and `high_stop_fourth_exclusion`. The strengthened `exactly_three_not_four` theorem also imports the authentic Agent 34 `ThreeConeProper`; source CI for this extension must be distinguished from the previous successful run. The local Lean 4.36.0-rc2 signature-matched check passed. No full Machine C halting decision or BB(6) maximality follows.

## New mathematical calculation: exact eventual fourth-return image density

The following is a **paper derivation with a deterministic exhaustive integer certificate** [four_step_density.cpp](four_step_density.cpp). It has **not yet been independently Lean-kernel checked** or independently peer reviewed. It strengthens Agent 45's already published paper result `delta(I_3)=261171/524288`, derived from the original-source complete inverse grammar and the earlier Agent 34 `I_2` theorem.

Our exact calculation gives

```
delta(I_4 | x odd)  =  7,132,041 / 16,777,216  = 0.42510277032852173
delta(I_4 | x even) = 28,708,239 / 67,108,864  = 0.42778609693050385
delta(I_4)          = 57,236,403 /134,217,728  = 0.42644443362951280
```

In particular, the exact asymptotic loss between the third and fourth images is

```
delta(I_3 \\ I_4) = 9,623,373 /134,217,728 = 0.07169971615076065.
```

For the high stopping gate `x=2*j+3`, which has **odd** first coordinate, the conditional density of `I_4` exclusions is therefore **9,645,175/16,777,216**, about **57.49%** of large high-parameter pairs. This is a density statement about necessary image admissibility. It is not a fraction of machine decisions, and it does not make the remaining candidate gates reachable.

### Derivation and finite certificate contract

Write `S=x+y`, `Q=S+(S mod2)`, `v=nu_2(Q)`. At sufficiently large coordinates, the complete original `secNext` inverse grammar provides one direct precursor `(S-2,(y-2)/2)` when `y` is even, and the following high-bounce precursors:

```
A_n = Q/2^(n+1) - (2 if S even else 3)
K_n = (S+y-A_n-7-3*n)/2
0 <= n <= v-2;
n even if y odd, n odd if y even.
```

Each arithmetic candidate is a real original source transition whenever the large-counter branch guards hold. The source inverse iff proves exhaustiveness. For all `x>=8`, `y>=1026`, `S>=2^25`, every candidate used in the finite reduction is within the exact eventual `I_3` region.

The Agent 34 two-return Boolean `H2` depends on `(S mod64,y mod64)`; it has 2448 accepted of 4096 cells. Agent 45's `I_3` calculation can be sharpened to a sufficient period of `(S mod2^15,y mod128)`, because for `v<=9` the largest predecessor depth is `n=v-2<=7`; its first coordinate modulo 128 requires only `Q mod2^(n+8)`, hence `Q mod2^15` suffices. The other valuations `v>=10` are universally in `I_3` by Agent 45's finite high-valuation proof. The executable reconstructs this reduced `H3` table, with exactly **2,089,368 positives in 4,194,304 cells**, and exhaustively compares it to the older period `2^17` on **16,777,216 comparisons, zero mismatches**. This period reduction is a paper argument with arithmetic checks, not a separately kernel-certified theorem.

For a fourth-image target with **`1<=v<=17`**, set `Q=2^v U` with odd `U`. The exact disjunction of `H3` on its direct and high parents depends only on

```
U mod 2^15 (odd),  S mod 2,  y mod 2^16.
```

This is because the high parent needs `A_n mod2^16` and `y mod2^16` to calculate `K_n mod128` and `(A_n+K_n) mod2^15`, and `n<=v-2` supplies `2^(v-n-1)>=2`. Each valuation stratum has **2^30 cases with x odd**, and equally many with x even. Every case is enumerated in the C++ certificate, without a random sample or simulation cutoff.

| v | x odd accepted / 2^30 | x even accepted / 2^30 |
|---:|---:|---:|
| 1 | 274440192 | 286642176 |
| 2 | 530436096 | 525312000 |
| 3 | 642079744 | 628834304 |
| 4 | 791199744 | 778722304 |
| 5 | 854609920 | 884670464 |
| 6 | 944963584 | 901599232 |
| 7 | 941314048 | 966672384 |
| 8 | 1013104640 | 1023234048 |
| 9 | 1046597632 | 1044987904 |
| 10 | 1065009152 | 1064882176 |
| 11 | 1066213376 | 1069219840 |
| 12 | 1073184768 | 1068310528 |
| 13 | 1070661632 | 1073741824 |
| 14 | 1073741824 | 1070727168 |
| 15 | 1070727168 | 1073741824 |
| 16 | 1073741824 | 1070727168 |
| 17 | 1073741824 | 1073741824 |

For `v>=18`, at least one of the genuine high-bounce parents with depth `n<=11` belongs to `I_3` in every residue case. To certify this infinite tail, test `v=18,...,28`. At each `v<28`, the twelve chosen depth expressions depend only on odd `U mod 2^(28-v)`, both `S` parities and `y mod2^16`. At `v>=28` the relevant quotient terms vanish modulo `2^16`, so the `v=28` case represents the entire infinite tail. The exact certificate tested all **11 finite valuation cases, with zero uncovered cells**, and hence the whole tail. The common geometric valuation law gives tail mass `P(v>=18)=2^-17`.

The resulting exact densities are obtained by **rational summation**, separately for first-counter parity:

```
delta(I4 | parity) =
  sum(v=1..17, accepted[v,parity] / (2^30 * 2^v)) + 2^-17.
```

The fixed residue modulus for eventual `I_4` membership may be taken as `(S mod2^32,y mod2^16)`, with all sufficiently large counter coordinates as above. The finite coordinate boundary contributes zero natural density.

### Why the high-stopping parameter density is legitimate

For `m>=16`, the original high stopping equation gives, modulo `2^32`,

```
S = (2*j+3)+k = j-3*m-2,
y = k = -j-3*m-5.
```

The affine map `(j,m) -> (S,y)` has determinant `-6`. Modulo any power of two, it covers every coordinate pair with odd first coordinate `x=S-y` with constant multiplicity two. Thus uniform `(j,m)` residue classes sample the odd-`x` image density exactly. The finitely many lower `m` rows do not affect the two-parameter limiting density.

## Evidence and next mathematical obligations

- **Kernel-certified original-source:** the four-edge obstruction, genuine blank nonreachability, and high-stopping lattice, as of CI 42600105398. The additional three-edge witness has a separate pending original-source CI check.
- **Finite exact arithmetic plus paper reduction:** complete fourth-image density, 17 valuation rows per parity, the finite tail cover, and the sharper third-image period. The C++ file contains the complete reproducible computation. No source Lean theorem yet states the full fourth-image density.
- **Open:** source-check the exact three-edge witness; intersect the complete `I_4` sieve with the strongest existing `highAllowed` filters and isolate genuinely new surviving high parameters; pursue a true complete blank-root decision. No exact six-state Busy Beaver value follows from any image-density bound.

Source dependencies: [complete section inverse](../agent3-c-bounce-inverse/SectionAllInverse.lean); [Agent 34 two- and three-edge theorem](../agent34-c-degree-profile/ThreeConeSource.lean); [Agent 45 full third-image certificate](../agent45-c-three-step/README.md); [prior Agent 4 two-versus-three and stopping diagonals](../agent4-c-three-ancestry/README.md).
