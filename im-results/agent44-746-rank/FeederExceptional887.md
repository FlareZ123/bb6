# Candidate exclusion for the subresidue n ≡ 887 (mod 13122)

**Status: proof blueprint for one 3-adic lift only; not a Lean theorem and not CI-verified.** This note records a small exact inverse-tree candidate for the distinguished t=1 odd predecessor of `fatal(n)=4·2^n−n−4`. It applies to the subresidue `n mod 13122 = 887), which is only one of the nine lifts of `n mod1458=887`. It must not be presented as an exclusion for the entire 1458-class.

## Scope correction: the 1458-class has nine distinct lifts

Write `n=887+1458k`, with `k=0,…,8` representing the nine residues modulo 13122. For each k, exact BigInt enumeration of the inverse tree of `x=oddPre n (fatal n)` was run at
`n₀=887+1458k+13122T`, for `T=0,1,2,10`.

| k | n₀ | v₃(2x+5), T=0,1,2,10 | tree nodes, T=0,1,2,10 | sampled topology |
|---:|---:|---|---|---|
| 0 | 887 | 4,4,4,4 | 6,6,6,6 | stable six-node chain |
| 1 | 2345 | 4,4,4,4 | 6,6,6,6 | stable six-node chain |
| 2 | 3803 | 5,5,5,5 | 10,14,21,14 | changes; deeper t=3/t=4 branches |
| 3 | 5261 | 4,4,4,4 | 6,6,6,6 | stable six-node chain |
| 4 | 6719 | 4,4,4,4 | 6,6,6,6 | stable six-node chain |
| 5 | 8177 | 6,7,6,7 | 10,13,10,13 | changes; higher valuation |
| 6 | 9635 | 4,4,4,4 | 22,28,17,22 | changes; deep even/odd branches |
| 7 | 11093 | 4,4,4,4 | 6,6,6,6 | stable six-node chain |
| 8 | 12551 | 5,5,5,5 | 9,15,9,22 | changes; deeper branches |

The maximum sampled tree has 28 nodes and depth 19 (k=6, T=1). Thus the six-node chain below is only a candidate for k=0 (and the same sampled topology occurs for k=1,3,4,7). The other four lifts k=2,5,6,8 need separate higher-valuation analysis. In particular, sampling `n=887+13122T` only probes k=0; it does not probe the other eight lifts. This corrects the earlier overbroad interpretation of the period-13122 experiments.

## Proposed quantified statement for k=0 only

Let `p=2^(n-2)`, `x=oddPre n (fatal n)`. The intended subresidue theorem is

```lean
theorem fatal_feeder_887_subresidue_root_exclusion (n : Nat)
    (hn : n % 13122 = 887) :
    ResetParent (oddPre n (fatal n)) (fatal n) ∧
      ¬ ReachC (2,0) (oddPre n (fatal n),0)
```

This excludes the distinguished odd feeder only on the subresidue `n≡887 mod13122`. It does not exclude the fatal target's even parent, other odd parents, the other eight lifts, or establish anything about BB(6) itself.

## Exact candidate inverse tree for k=0

For `n≡887 mod13122`, the complete representative enumeration at `n=887` gives:

```text
x
├── E_(n-2) ──> u       [terminal: no parent]
└── O_(2,n-4) ──> a
                    └── E_(n-4) ──> b
                                           └── O_(0,n-5) ──> c
                                                                  └── E_(n-5) ──> d
                                                                                   [terminal: no parent]
```

The tree has six nodes and five edges. The proof obligation is exhaustive parent classification, not merely showing that the displayed edges exist:

- `x` has exactly the two displayed parents `u` and `a`.
- `u` has no parent.
- `a` has exactly the even parent `b`.
- `b` has exactly the odd t=0 parent `c`.
- `c` has exactly the even parent `d`.
- `d` has no parent.

If `x` were root-reachable, its last reset parent would therefore be `u` or `a`. The first is impossible; the second forces reachability successively through `b,c,d`, also impossible.

## Period and modular certificate for k=0

The modulus is `13122=2·3^8). Since `φ(3^8)=4374) and `4374 | 13122`, the power `2^(n-2)` has a fixed residue modulo `6561=3^8) whenever `n mod13122=887`. For this subresidue:

```text
n mod 6561 = 887
p mod 6561 = 2^885 mod 6561 = 3869
2^4374 mod 6561 = 1
```

The identity `2^4374 mod6561=1` can be kernel-checked directly (as in the existing `pow_period486_729` proof). This certificate does **not** apply to the other eight lifts `887+1458k` with k≠0; each has different residues modulo 6561. Existing `growth` gives `10000*n+10000 ≤ p` for this range.

Define the successive heights by the displayed inverse formulas:
```text
x = (56*p - 17*n - 39)/9
u = 2*x - 8*p - n + 2
a = 8*((2*x+5)/27) - 2*p - n - 1
b = 2*a - 2*p - n + 4
c = 2*((2*b+5)/3) - p - n
d = 2*c - p - n + 5
```

Their exact affine identities and modular residues for k=0 are:

| Height | Exact identity | Residue certificate |
|---|---|---|
| `x` | `9*x + 17*n + 39 = 56*p` | `x mod729=524`; `(2*x+5) mod729=324` |
| `u` | `9*u + 43*n + 60 = 40*p` | `u mod729=558`; hence `u mod3=0` |
| `a` | `243*a + 515*n + 507 = 410*p` | `a mod27=2`; `(2*a+5) mod27=9` |
| `b` | `243*b + 1273*n + 42 = 334*p` | `b mod27=23`; `(2*b+5) mod9=6` |
| `c` | `729*c + 5821*n - 2262 = 607*p` | `c mod9=3`; hence `c mod3=0` |
| `d` | `729*d + 12371*n - 8169 = 485*p` | `d mod9=7`; hence `d mod3=1` |

The residue data follow by reducing the affine identities using `p mod6561=3869` and `n mod6561=887`; they are fixed for the whole k=0 subresidue.

## Dyadic locations and odd-quotient filters for k=0

All intervals below follow from the affine identities and `10000*n+10000 ≤ p`; their margins are linear inequalities intended for `omega`.

| Height / quotient | Required location |
|---|---|
| `x` | even band at scale `n-2`: `6*p-1 ≤ x ≤ 8*p-3` |
| `u` | middle-low gap at scale `n-2`: `4*p-3 < u < 6*p-1` |
| `a` | even band at scale `n-4`: `6*2^(n-4)-1 ≤ a ≤ 8*2^(n-4)-3` |
| `b` | middle-low gap at scale `n-4`: `4*2^(n-4)-3 < b < 6*2^(n-4)-1` |
| `c` | even band at scale `n-5`: `6*2^(n-5)-1 ≤ c ≤ 8*2^(n-5)-3` |
| `d` | middle-low gap at scale `n-5`: `4*2^(n-5)-3 < d < 6*2^(n-5)-1` |

Odd-branch quotient tests:

1. For `x`, `v₃(2*x+5)=4`: the residue 324 modulo729 is divisible by81 but not243. For `t=0,1,3`, the odd-band parameters `(2*x+5)/3`, `2*(2*x+5)/9`, and `8*(2*x+5)/81` lie respectively in the gaps `(4p,6p)`, `(2p,3p)`, and `(p,3p/2)`. For `t=2`, `4*(2*x+5)/27` lies in the odd band at scale `n-4), giving the unique odd parent `a`. Exponents `t≥4` contradict `243 ∤ 2*x+5`.
2. For `a`, `v₃(2*a+5)=2): its residue 9 modulo27 is divisible by9 but not27. The t=0 parameter `(2*a+5)/3` lies in `(p,3p/2)`; the t=1 parameter `2*(2*a+5)/9` lies in `(p/2,3p/4)). Both are odd-band gaps; `t≥2` contradicts `27 ∤ 2*a+5`. Since `a` is in its even band, its only parent is `b`.
3. For `b`, `(2*b+5) mod9=6), so only `t=0) is possible. Its quotient `(2*b+5)/3` lies in the odd band at scale `n-5), giving `c). The middle-low gap rules out even parents.
4. `c mod3=0), so it has no odd parent; its even-band scale is unique, giving `d).
5. `u` and `d` each lie in a middle-low gap and have residue different from 2 modulo3. Hence neither has an even nor an odd parent, by `root_excludes_nonimage` and `no_even_band_from_gap`.

The quotient gaps can be expressed using the existing `odd_gap` lemma: `2*2^k < q < 3*2^k` excludes every odd image band. The only non-gap odd quotients are the displayed parent at t=2 for x and t=0 for b.

## Lean implementation plan for k=0

Reuse `CascadeFeederExceptional.odd_gap`, `no_even_band_from_gap`, `parent_backward`, `even_backward`, and `middle_low_unique_odd_t0` from `FeederExceptionalStep.lean`. Add one helper for a target in an even band whose t=0 and t=1 odd quotients lie in gaps and whose 27-divisibility obstruction rules out t≥2; this proves the unique-even-parent claim for `a`. For `x`, destruct `ResetParent` and classify the even arm by `even_band_unique), while the odd arm is forced to t=2 by the four quotient cases and to scale n-4 by `odd_band_scale_unique). A small `parent_backward_or` lemma can turn root reachability of x into reachability of u or a.

No Lean file for this candidate has yet been written. The six-node tree at k=0 and all finite lift samples are discovery evidence only; the k=0 modular proof and every interval/parent classification still need kernel formalization. The other four high-complexity lifts k=2,5,6,8 are separate open branches and require the higher 3-adic analysis already under way in Agent 7/10's Hensel work.

## Lean formalization draft (12 November 2026)

The single k=0 subresidue has now been formalized as an intermediate Lean draft in [FeederExceptional887.lean](FeederExceptional887.lean).

- `CascadeFeeder887.narrow_exact_two_t2` is the reusable t=2 parent classifier under 243-nondivisibility. It proves that an even-band target with the displayed t=2 odd parent has exactly two immediate parents: the even parent and that t=2 parent. The odd t=0,1,3 branches are eliminated by the three quotient gaps; t≥4 is eliminated by 243-nondivisibility.
- `CascadeFeeder887.fatal_feeder_887_subresidue_root_exclusion` proves the exact tree above for every `n % 13122 = 887`, including both terminal branches u and d.
- `CascadeFeeder887.fatal_root_iff_even_parent_887_subresidue` composes this exclusion with the existing eight-class fatal-parent theorem and reduces fatal-root reachability to the even fatal predecessor on this one lift.
- `CascadeFeeder887.even_parent_formula_887` identifies that predecessor exactly as `16*2^(n-2)-3*n-7`; `fatal_root_iff_even_parent_formula_887` gives the corresponding explicit reachability equivalence. The even predecessor itself remains unresolved.

The module is included after `FeederExceptionalFamily.lean` in the manual-only workflow [agent44-746-fanin.yml](../../.github/workflows/agent44-746-fanin.yml). **This is still an uncompiled draft pending unchanged-source Lean CI**; do not cite the theorem as kernel-verified until the workflow completes and its two `#print axioms` outputs are checked. The scope remains exactly one of the nine lifts of n mod1458=887.

## Exact modular certificates for the five stable lifts

The same six-node tree shape is observed for the five lifts
`n = 887 + 1458 k` with `k ∈ {0,1,3,4,7}`, i.e.
`n mod 13122 ∈ {887,2345,5261,6719,11093}`. The following table gives the exact modular data for the affine chain
`x,u,a,b,c,d` defined above. It is computed at each least nonnegative representative; it holds for every lift `n=r+13122T`, because `n mod 6561` is fixed and `2^4374 ≡ 1 (mod 6561)` (hence `2^(n-2) mod 6561` is fixed).

| k | r | n mod 6561 | p mod 6561 | (2x+5) mod 729 | u mod 729 | a mod 27 | (2a+5) mod 27 | b mod 27 | (2b+5) mod 9 | c mod 9 | d mod 9 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 0 | 887 | 887 | 3869 | 324 | 558 | 2 | 9 | 23 | 6 | 3 | 7 |
| 1 | 2345 | 2345 | 1682 | 405 | 639 | 26 | 3 | 17 | 3 | 4 | 0 |
| 3 | 5261 | 5261 | 3869 | 567 | 72 | 20 | 18 | 5 | 6 | 6 | 4 |
| 4 | 6719 | 158 | 1682 | 648 | 153 | 17 | 12 | 26 | 3 | 7 | 6 |
| 7 | 11093 | 4532 | 1682 | 162 | 396 | 8 | 21 | 8 | 3 | 1 | 3 |

The table shows the uniform valuation/residue conditions needed by the six-node argument:
- `(2x+5) mod 729` is always divisible by 81 and nonzero modulo 243, so the t=2 odd parent is the only possible odd parent after the t=0,1,3 quotient gaps.
- `u mod 729` is always 0 modulo 3, excluding odd parents of u.
- `(2a+5) mod 27` is always divisible by 3 and nonzero modulo 27; the t=0,1 quotient gaps therefore leave only the displayed even parent b.
- `(2b+5) mod 9` is always divisible by 3 and nonzero modulo 9, leaving only the displayed t=0 odd parent c.
- `c mod 9` and `d mod 9` are never 2 modulo 3, excluding their odd parents.

The affine dyadic-band/gap inequalities are uniform in all five lifts once the common growth bound is available. Thus this table strongly supports extending the Lean proof to all five stable lifts by replacing the k=0 residue equalities with the five-way modular disjunctions. **That five-lift extension is not yet formalized**; the current Lean draft remains restricted to `n mod 13122 = 887`.

## Open even-predecessor chain (arithmetic lead, not yet formalized)

For the k=0 lift, the explicit even predecessor is
`y₀ = 4*2^n - 3*n - 7`. Its same-scale even parent at `k=n-1` is
`y₁ = 2*y₀ - 8*2^(n-1) - (n-1) = 4*2^n - 7*n - 13`.
More generally, while the chain remains in the scale-`n-1` even band, write
`y_m=4*2^n-D_m`; the same-scale even-parent recurrence is
`D₀=3*n+7`, `D_(m+1)=2*D_m+n-1`.
The band condition is exactly `3≤D_m≤2^n+1`.

Modulo 3, `D_m` alternates `1,0`, so `y_m mod3` alternates `1,2`. Terms with `y_m mod3=1` have no odd parent at all. For terms with `y_m mod3=2`, the t=0 odd quotient
`q₀=(2*y_m+5)/3=(8*2^n-2*D_m+5)/3`
lies strictly in `(2*2^n,3*2^n)` throughout the even-band range, so the t=0 branch is excluded by `odd_gap`.

**Do not extend this t=0 gap argument to t≥1.** The actual odd-parent band value at exponent t is `2^t*(2*y_m+5)/3^(t+1)=(2/3)^t*q₀), not `2^t*q₀`. In fact `D_m mod9` cycles `4,3,1,6,7,0`; for odd m, `(2*y_m+5) mod9` cycles `3,6,0`, so t=1 divisibility can occur when `m≡5 (mod 6)`. The higher-t branches require the nested 3-adic analysis; the first departure from the scale-`n-1` even band may also enter a lower-scale band rather than terminate. This is an open route to the even predecessor, not a completed root exclusion.
