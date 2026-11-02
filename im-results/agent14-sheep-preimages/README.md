# Sheep Machine: exact one-step predecessors of the `3·2^j` section family

**Agent 14, 2026-11-02. Status: intermediate analytical theorem, not a BB(6) decision.**

Machine: `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE` (the Sheep Machine, a BB(6) holdout).
Google DeepMind's [Lean-certified machine acceleration](https://google-deepmind.github.io/cryptids/BusyBeaver/BB6/M_1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_HHH1LE/) enters `(m,k)=(0,2)` from the blank tape and has the rules

```
(0,0) -> (0,2)
(0,k+1) -> (2,k)
(1,k) -> HALT
(2r,k), r>=1 -> (3r+k,1)
(2r+3,k) -> (r,r+k+4)
```

One transition from `(0,2)` enters `(2,1)`. The standard one-argument return section starts at `t=m+3=5`, `k=1`; this is also derived in the [Busy Beaver Wiki's Sheep Machine analysis](https://wiki.bbchallenge.org/wiki/1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE). Let `a=v₂(t)` and `u=t/2^a` (so `u` is odd). Its exact partial return map is

```
F(t) = HALT                     if u=1
F(t) = t+a+3                    if u=3
F(t) = t+a+(u-1)/2              if u>=5.
```

The map's equivalence to the published counter accelerator is already prior art. The new result below concerns its **complete inverse image** of the exceptional `u=3` family.

## Theorem: complete incoming-edge classification

For every integer `j>=2`, all predecessors `t>=3` satisfying `F(t)=3·2^j` lie in exactly the following families. Whenever a row's condition holds, the displayed source really is a predecessor:

| Valuation `a=v₂(t)` | Necessary and sufficient condition on `j` | Unique source `t` |
|---|---|---|
| `a=1` | `j>=4`, `j≡0 (mod 4)` | `2(6·2^j−1)/5` |
| `a=2` | `j>=3`, `j` odd | `4(2^(j+1)−1)/3` |
| `a=3` | `j>=5`, `j≡5 (mod 8)` | `8(6·2^j−5)/17` |
| `a=0` or `a>=4` | never | none |

Sources with odd part `3` supply no additional predecessor for `j>=2`. The only such incoming edge among **all** `3·2^j` targets is `3 -> 6` when `j=1`.

**All-time blank-start corollary.** For each natural `q`, the actual return trajectory `5,F(5),F²(5),...`, while defined, **never visits `3·2^(4q+2)`**. Indeed the theorem says every one of these infinitely many states has no incoming transition from any possible source, and the initial state `5` is different. This eliminates one full congruence class of `u=3` targets with an unconditional infinite reachability exclusion. It leaves the remaining three classes, all power-of-two halting targets, and the BB(6) value unresolved.

## Complete arithmetic proof

For odd part `u>=5`, put `t=2^a u`. The equation `F(t)=3·2^j`, multiplied by two, is

```
6·2^j = (2^(a+1)+1)u + 2a−1.                 (1)
```

- **`a=0`:** Equation (1) reads `6·2^j=3u−1`, impossible modulo three.
- **`a=1`:** It reads `6·2^j=5u+1`, so `2^j≡1 (mod 5)`, exactly `j≡0 (mod 4)`. The resulting quotient is odd, and it is `>=5` exactly from `j=4` onward.
- **`a=2`:** Division by three yields `2^(j+1)=3u+1`, possible exactly for odd `j`; the quotient is odd and reaches `5` at `j=3`.
- **`a=3`:** Modulo seventeen gives `2^j≡15≡2^5 (mod 17)`. Since two has multiplicative order eight modulo seventeen, this means `j≡5 (mod 8)`; the quotient is odd and first reaches `11` at `j=5`.

It remains to rule out **every `a>=4` and every exponent `j`**, with no computational cutoff. Write `P=2^a`, `M=2P+1`, and `D=2a−1`. The elementary exponential bounds

```
0 < D < P/2,       P/2 > a,       P/4 > a−1       (a>=4)
```

hold at `a=4` and persist by doubling `P` when `a` increments. Equation (1) implies `6·2^j ≡ D (mod M)`. Because `2^(a+1) = M−1 ≡ −1 (mod M)`, Euclidean division of `j` by `a+1` reduces this congruence to

```
6·2^r ≡ +D or −D (mod M),       0<=r<=a.      (2)
```

There are three exhaustive cases.

1. **`r=0`:** `6` equals neither `D` (which is at least seven) nor `M−D` (which exceeds six); both representatives lie strictly between zero and `M`.
2. **`r=a`:** `6·2^a = 3M−3`, whose residue is `M−3`. This is neither `D` nor `M−D` because `3<D<M−3`.
3. **`1<=r<=a−1`:** Put `V=6·2^r`. Then `V` is even, `D` is odd, and `0<V+D<2M`. Therefore (2) forces `V=M+D` or `V=M−D`. Dividing either equality by two gives `3·2^r=P+a` or `3·2^r=P−a+1`. If `r<=a−2`, then `3·2^r <=3P/4 <P−a+1` since `P/4>a−1`, excluding both equations. If `r=a−1`, then `3·2^r=3P/2>P+a` because `P/2>a`, again excluding both equations.

Thus no source with `a>=4` exists. For odd part `u=3`, `F(3)=6`; for `a>=1`, `3·2^a < F(3·2^a) < 3·2^(a+1)` (since `a+3<3·2^a`), so no `3·2^j` can be its output. Sources with `u=1` halt rather than return. This completes the inverse-image classification and corollary.

## Independent reproducibility checks

`check.py` verifies the section map against the **published two-counter transition rules** at all `199,997` integers `t` from 3 through 199,999, checks the complete predecessor enumeration at exponents `0..79`, and verifies the absence of predecessors at `400` further exponents `j=4q+2` through 1,598. It also simulates 20,000 return steps from the real section start `t=5`, observing no halt or `3·2^j` family encounter. All of these checks passed under Python 3 on 2026-11-02. They are finite consistency checks; the preceding proof establishes the universal assertion.

**Limitations:** This proof is written mathematical reasoning and has **not** been kernel-checked in Lean. It proves a new-to-this-repository infinite absence-of-incoming-edges statement in the independently published return map, and it does **not** establish nonhalting of the Sheep Machine. The result's novelty beyond the present repository has not been exhaustively established; keep it in `im-results/` until cross-review. The relevant wiki already gives the one-variable reduction, but its current public discussion does not state this full `3·2^j` inverse classification.
