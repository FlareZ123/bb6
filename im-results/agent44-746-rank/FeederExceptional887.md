# Candidate all-index exclusion for the exceptional feeder class 887

**Status: proof blueprint, not a Lean theorem and not CI-verified.** This note records a small exact inverse-tree candidate for the distinguished t=1 odd predecessor of `fatal(n)=4·2^n−n−4`. It must not be promoted to `results/` or described as a proved all-index result until the proposed parent exhaustiveness and inequalities are formalized against the unchanged source-C grammar.

## Proposed quantified statement

Let `p=2^(n-2)`, `x=oddPre n (fatal n)`. The intended theorem is

```lean
theorem fatal_feeder_887_root_exclusion (n : Nat)
    (hn : n % 13122 = 887) :
    ResetParent (oddPre n (fatal n)) (fatal n) ∧
      ¬ ReachC (2,0) (oddPre n (fatal n),0)
```

This excludes the distinguished odd feeder only. It does not exclude the fatal target's even parent, other odd parents, or establish anything about BB(6) itself.

## Exact candidate inverse tree

The complete representative enumeration at `n=887` gives the following parent graph. Labels `E_m` and `O_{t,m}` mean the even and odd arms of the exact `ResetParent` relation, respectively.

```text
x
├── E_(n-2) ──> u       [terminal: no parent]
└── O_(2,n-4) ──> a
                    └── E_(n-4) ──> b
                                           └── O_(0,n-5) ──> c
                                                                  └── E_(n-5) ──> d
                                                                                   [terminal: no parent]
```

Thus the tree has six nodes and five edges. The key proof obligation is exhaustive parent classification, not merely showing that the displayed edges exist:

- `x` has exactly the two displayed parents `u` and `a`.
- `u` has no parent.
- `a` has exactly the even parent `b`.
- `b` has exactly the odd t=0 parent `c`.
- `c` has exactly the even parent `d`.
- `d` has no parent.

If `x` were root-reachable, its last reset parent would therefore be `u` or `a). The first is impossible; the second forces reachability successively through `b,c,d), also impossible.

## Period and modular certificate

The proposed period is `13122 = 2·3^8`. Since `φ(3^8)=4374` and `4374 | 13122`, the power `2^(n-2)` has a fixed residue modulo `6561=3^8) whenever `n % 13122 = 887`. The exact residue is

```text
n mod 6561 = 887
p mod 6561 = 2^885 mod 6561 = 3869
```

The identity `2^4374 mod 6561 = 1` can be kernel-checked directly (as in the existing `pow_period486_729` proof). The period also fixes n modulo 6561. Existing `growth` gives `10000*n+10000 ≤ p` for this range.

Define the successive heights by the displayed inverse formulas:
```text
x = (56*p - 17*n - 39)/9
u = 2*x - 8*p - n + 2
a = 8*((2*x+5)/27) - 2*p - n - 1
b = 2*a - 2*p - n + 4
c = 2*((2*b+5)/3) - p - n
d = 2*c - p - n + 5
```

Their exact affine identities and modular residues are:

| Height | Exact identity | Residue certificate |
|---|---|---|
| `x` | `9*x + 17*n + 39 = 56*p` | `x mod 729 = 524`; `(2*x+5) mod 729 = 324` |
| `u` | `9*u + 43*n + 60 = 40*p` | `u mod 729 = 558`; hence `u mod 3 = 0` |
| `a` | `243*a + 515*n + 507 = 410*p` | `a mod 27 = 2`; `(2*a+5) mod 27 = 9` |
| `b` | `243*b + 1273*n + 42 = 334*p` | `b mod 27 = 23`; `(2*b+5) mod 9 = 6` |
| `c` | `729*c + 5821*n - 2262 = 607*p` | `c mod 9 = 3`; hence `c mod 3 = 0` |
| `d` | `729*d + 12371*n - 8169 = 485*p` | `d mod 9 = 7`; hence `d mod 3 = 1` |

The residue data are obtained by reducing the affine identities using `p mod 6561=3869` and `n mod 6561=887`. They are fixed for the whole 13122-adic family.

## Dyadic locations and odd-quotient filters

All intervals below follow from the affine identities and `10000*n+10000 ≤ p`; their margins are linear inequalities that `omega` should discharge.

| Height / quotient | Required location |
|---|---|
| `x` | even band at scale `n-2`: `6*p-1 ≤ x ≤ 8*p-3` |
| `u` | middle-low gap at scale `n-2`: `4*p-3 < u < 6*p-1` |
| `a` | even band at scale `n-4`: `6*2^(n-4)-1 ≤ a ≤ 8*2^(n-4)-3` |
| `b` | middle-low gap at scale `n-4`: `4*2^(n-4)-3 < b < 6*2^(n-4)-1` |
| `c` | even band at scale `n-5`: `6*2^(n-5)-1 ≤ c ≤ 8*2^(n-5)-3` |
| `d` | middle-low gap at scale `n-5`: `4*2^(n-5)-3 < d < 6*2^(n-5)-1` |

The odd-branch quotient tests are:

1. For `x`, `v₃(2*x+5)=4): its residue 324 modulo 729 is divisible by 81 but not 243. For `t=0,1,3`, the odd-band parameters `(2*x+5)/3`, `2*(2*x+5)/9`, and `8*(2*x+5)/81` lie respectively in the gaps `(4p,6p)`, `(2p,3p)`, and `(p,3p/2)`. For `t=2`, `4*(2*x+5)/27` lies in the odd band at scale `n-4`, giving the unique odd parent `a). Exponents `t≥4` contradict `243 ∤ 2*x+5`.
2. For `a`, `v₃(2*a+5)=2): its residue 9 modulo 27 is divisible by 9 but not 27. The t=0 parameter `(2*a+5)/3` lies in `(p,3p/2)); the t=1 parameter `2*(2*a+5)/9` lies in `(p/2,3p/4)). Both are odd-band gaps; `t≥2` contradicts `27 ∤ 2*a+5`. Since `a` is in its even band, its only parent is `b).
3. For `b`, `(2*b+5) mod 9=6`, so only `t=0) is possible. Its quotient `(2*b+5)/3` lies in the odd band at scale `n-5`, giving `c). The middle-low gap rules out even parents.
4. `c mod 3=0`, so it has no odd parent; its even-band scale is unique, giving `d).
5. `u) and `d) each lie in a middle-low gap and have residue different from 2 modulo 3. Hence neither has an even nor an odd parent, by `root_excludes_nonimage` and `no_even_band_from_gap`.

The quotient gaps can be expressed directly using the existing `odd_gap` lemma: `(2*2^k < q ∧ q < 3*2^k)` excludes every odd image band. The only non-gap odd quotient is the displayed parent at t=2 for x and t=0 for b.

## Lean implementation plan

Reuse `CascadeFeederExceptional.odd_gap`, `no_even_band_from_gap`, `parent_backward`, `even_backward`, and `middle_low_unique_odd_t0` from `FeederExceptionalStep.lean`. Add one helper for a target in an even band whose t=0 and t=1 odd quotients lie in gaps and whose 27-divisibility obstruction rules out t≥2; this proves the unique-even-parent claim for `a`. For `x`, destruct `ResetParent` and classify the even arm by `even_band_unique), while the odd arm is forced to t=2 by the four quotient cases and to scale n-4 by `odd_band_scale_unique). A small `parent_backward_or` lemma can turn root reachability of x into reachability of u or a.

No Lean file for this candidate has yet been written. The finite tree at n=887 and the finite period samples are discovery evidence only; the period-13122 modular proof and every interval/parent classification above still need kernel formalization.
