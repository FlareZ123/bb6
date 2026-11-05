# Four 2-adic sectors of unbounded Sheep power-gate indegree

**Agent 17, 2026-11-05. Intermediate graph theorem.** No blank-orbit reachability conclusion, Sheep holdout decision, BB(6) bound, or external novelty assessment follows.

## Exact theorem

Let the terminal target be `Y=2^j`, where `j>=2` is an integer with `v2(j)=r` for `r∈{1,2,3,4}`, and let `k=v3(j)`. Use the corresponding row:

| `r` | source `a=2^r−1` | `M=2^(a+1)+1` | allowed hidden lengths `h=H+Pt` | minimum `k` |
|---:|---:|---:|---|---:|
| 1 | 1 | 5 | `1+2t` | 1 |
| 2 | 3 | 17 | `1+16t` | 1 |
| 3 | 7 | 257 | `92+256t` | 91 |
| 4 | 15 | 65,537 | `43005+65536t` | 43004 |

For each nonnegative `t` with `h<=k+1`, the values

```text
q=(2^j−1)/3^h; K=2a−3;
v=(2^(h+1)*q−K)/M; x=2^a*v
```

are positive integers, `q,v` odd, `v>=5`, and `x` is a legal generic Sheep first-even predecessor with `E(x)=2^j` and exactly `h` hidden odd steps. These are **all** the possible incoming parents of source 2-valuation `a`, since the exceptional cofactor-three source cannot directly return a power. Distinct `h` produce distinct sources. Their exact number is

```text
floor((k+1−H)/P)+1.
```

Consequently the direct power-gate indegree is unbounded in each exponent sector `v2(j)=1,2,3,4` as `v3(j)→∞`. The exponent `j` can have other odd factors. The `r=1` case was [previously established](UNBOUNDED-POWER-FANIN.md); `r=2` is [our new valuation-three theorem](A3-POWER-FANIN.md). The valuation-seven and valuation-fifteen sectors are companion extensions.

## Proof

For a legal generic source `x=2^a*v` (`a>=1`, odd `v>=5`), the exact published Sheep source map is

```text
2F(x)=(2^(a+1)+1)*v+2a−1.
```

Writing `F(x)−1=2^h*q` with odd `q` gives `E(x)=1+3^h*q`. Therefore `E(x)=2^j` is equivalent to

```text
3^h*q=2^j−1; M*v=2^(h+1)*q−(2a−3).  (1)
```

Since `j` is even, the elementary 3-adic lifting identity `v3(2^j−1)=1+v3(j)=k+1` makes `q` integral and odd precisely for `0<=h<=k+1`.

With `a=2^r−1`, we have `M=2^(2^r)+1`. As `j=2^r*m` with odd `m`, `2^j≡−1 modM`. Each listed `M` is coprime to `6*(2a−3)`; consequently equation (1) is equivalent modulo `M` to

```text
g^h ≡ R (mod M);
g=3*(2^−1) mod M; R=−4*(2a−3)^−1 mod M.  (2)
```

The exact residue data, independently checked with full integer modular exponentiation, are:

| `a` | `K=2a−3` | `g modM` | exact order `P` | `R` | `H` |
|---:|---:|---:|---:|---:|---:|
| 1 | -1 | 4 | 2 | 4 | 1 |
| 3 | 3 | 10 | 16 | 10 | 1 |
| 7 | 11 | 130 | 256 | 23 | 92 |
| 15 | 27 | 32770 | 65536 | 33982 | 43005 |

For each row, `g^P≡1`, `g^(P/2)≡−1`, and `g^H≡R` modulo `M`. Since `P` is a power of two, these calculations prove its *exact* order, and (2) holds exactly when `h≡H modP`.

Integrality and oddness of `v` follow from (2) and (1). For `a=7,15`, `h>=92,43005` makes `2^(h+1)*q >=5M+K`; for `a=1` use `j>=6`, the earlier [cofactor bound](UNBOUNDED-POWER-FANIN.md); for `a=3`, `j>=12` gives either `q>=1365` at `h=1`, or `h>=17`. Hence all `v>=5`, and substitution in (1) gives the actual `F/E` transition. Since `M*v+K=2*(2/3)^h*(2^j−1)` strictly decreases with `h`, no two values coincide. The [source-genericity theorem](SPECIAL-SOURCE.md) excludes every exceptional `v=3` predecessor of a power.

## Evidence and boundary

[fermat_fanin_verify.py](fermat_fanin_verify.py) checks four exact orders, discrete logarithms, modular construction identities, and reproducible small literal Sheep transitions. The conditional all-natural source constructor for `a=3` passed Lean 4.36.0-rc2 in [A3PowerFanin.lean.xz.b64](A3PowerFanin.lean.xz.b64); the `a=7` constructor passed in [A7PowerFanin.lean.xz.b64](A7PowerFanin.lean.xz.b64); the all-natural `a=15` modular congruence passed in [A15PowerFanin.lean.xz.b64](A15PowerFanin.lean.xz.b64). Restore verified sources using [reconstruct_fanin_all.py](reconstruct_fanin_all.py). Local axiom audits list only `propext, Quot.sound`; the all-k lifting/count proofs and `a=15` legality remain written mathematics.

This uses the genuine published even-section return formula, previously bridged to the unchanged original Turing-machine source in [CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547), but the new Lean files do not import that upstream source. The actual blank-entry orbit from **10** might avoid every listed source. The machine/BB(6) problem remains open. This report belongs in `im-results/`, pending independent mathematical and novelty review.
