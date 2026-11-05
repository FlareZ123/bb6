# Universal phase-shift transfer reduces sevenfold Sheep 648 proof to 343 checks

Agent 14, 2026-11-05 19:36 UTC. Intermediate constructive proof reduction, locally Lean checked. The all-family source-integrated theorem remains pending. This note supplements [README.md](README.md) and [Z-SOURCE-LEAN.md](Z-SOURCE-LEAN.md).

## General Lean theorem

Locally Lean 4.36.0-rc2 proved `SheepPeriodicExclusionShift.transfer_forbidden`, with axiom audit exactly `[propext, Quot.sound]`, no `sorryAx`. For natural `m,o,R,P,delta,B,t,w` such that `1<m`, `2^o mod m=1`, `P*t=delta+o*w`, and

```
∀ k, (2^(R+P*k)+B) % m ≠ 0
```

the theorem derives, for **every natural k**,

```
(2^(R+delta+P*k)+B) % m ≠ 0.
```

Its proof rewrites `R+P*(k+t) = (R+delta+P*k)+o*w` and uses the previously proved `Sheep648Period.pow_mod_period`. This consumes an entire phase's exclusions using a single constructive shift witness `(t,w)`, without enumerating a new complete period.

## Arithmetic compression for 648+17496k

For root `(s,b,d)=(0,0,1)` and its common child `(8,-1228,2187)`, the baseline `j=648+122472k` has 57 low-valuation rows and 194 full period representatives. For each new phase `delta=17496*r`, `r=1,...,6`, **51 of those 57 rows** have `gcd(order_m(2),122472) | delta`. The constructive algorithm finds `t,w≥0` with `122472*t=delta+order_m(2)*w` and verifies the exact modular-power identity. All 306 witnesses were checked.

Only the same six rows fail phase equivalence, with `q=order_m(2)/gcd(order_m(2),122472)=1` in each case:

| Inverse node | hidden h | source a | m | order of 2 |
|---|---:|---:|---:|---:|
| root | 2 | 6 | 1161 | 126 |
| root | 3 | 6 | 3483 | 378 |
| root | 4 | 6 | 10449 | 1134 |
| root | 5 | 6 | 31347 | 3402 |
| common child | 0 | 6 | 282123 | 30618 |
| common child | 0 | 13 | 35833995 | 20412 |

Their 36 fresh checks show only the root's `h=3,a=6` row survives, and only in phase `r=2`, precisely producing new node `Z=(2^(j+10)-16576)/3483`. The 17 Z-leaf rows require 113 complete-period representatives, with source-equation impossibility already locally Lean certified in [Z-SOURCE-LEAN.md](Z-SOURCE-LEAN.md).

Therefore the entire sevenfold family may be certified from the common base and transport using just **110 distinct low-valuation obligations and 343 full-period representatives**, instead of naively proving 416 rows and 1471 period representatives independently. This is a **4.29x reduction in representative checks** (1471/343). Hidden-h uniform bounds, exceptional source gap inequalities, and high-a source gap bounds are unchanged across phases and reused from the common node equations at base 648.

## Reproducibility

The standalone standard-library verifier `sheep648_shift_compression.py` was run successfully in the same directory as `sheep648_tight_period.py`. SHA256 is `a4e773ec8fe454069fba6110f6a591c739e0ae576d62b1a590c9934e2332ce38`. This standalone file is a user-visible artifact of the invocation and is not currently in the GitHub tree. It independently verifies every shifted congruence identity at all complete-period representatives and the six exact non-equivalent rows per phase. The phase-shift Lean proof source is the separate user artifact `SheepPeriodicExclusionShift.lean`, SHA256 `6ef6013c0f570cb7dd0fb37eb79419272181b85ecae07811a0461032314f0621`.

Next formal step: compile the existing baseline root and child low modular theorems, instantiate `transfer_forbidden` with these 306 explicit arithmetic witnesses, prove the 36 remaining exact residues, and consume the already locally kernel-checked Z leaf and true original-source inverse splitter in the finite inverse DAG theorem. No BB(6) upper bound or whole Sheep resolution follows yet.