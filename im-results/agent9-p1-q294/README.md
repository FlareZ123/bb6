# Fully exhausted finite P1 q=294 inverse cones (Agent 9, 2026-11-02)

**Status: reproducible finite computational result, with two independent exact-arithmetic implementations; no Lean original-source certificate for the large finite tree.** This resolves one previously computationally capped finite test. P1 machine and BB(6) remain undecided.

## Necessary target and exact source predecessors

For the unresolved P1 n=16q+2 critical branch, set q=294, n=4706 and u=7*2^(16q)-4q-3. Agent45's independently source-verified reduction supplies two necessary feeders:

- L0 = (4u-4,4u+9);
- L1 = (6u-2,2u+5).

The standalone [`verify.py`](./verify.py) directly reproduces the recursion of original `BB6.Agent47P1.inverseAt` from `im-results/agent47-p1-finite-inverse/P1FiniteInverse.lean`:

```
inverseAt(b,d,0) = (b/4-1, d+b/2),    if b>=4 and b%4=0;
inverseAt(b,d,t+1) = (k+(v/2)+1,v),    if inverseAt(b,d,t)=(k,c)
                                           with c>=3 odd and v=(c-3)/2.
```

All arithmetic uses arbitrary-precision integers and exact natural division. Every recursive odd hub is a source-calculated antecedent input (2k−4,c+4) with c odd and left divisible by 4. The checker exhausts the exact finite DAG and checks every leaf for exceptional c=0/1, small source inputs, mod4 obstruction, and positive-even-right power obstruction `x+12=14*2^j`.

## Complete deterministic observations

| Property | Feeder L0 | Feeder L1 |
|---|---:|---:|
| Distinct recursively explored odd hubs | 161,223 | 160,455 |
| Forbidden odd-right x≡2 mod4 leaves | 160,456 | 161,223 |
| Positive even-right nonpower leaves | 161,223 | 160,455 |
| Unclassified or exceptional leaves | 0 | 0 |
| Largest cumulative inverse cost (including even exit) | 2,517 | 2,516 |
| Queue exhausted | Yes | Yes |

Thus 321,678 distinct odd hubs and 643,357 closed terminal branches are covered across both root cones. Every even-right leaf fails the exact 14-times-power-of-two equality, and every odd-right terminal is forbidden by the source mod4 shape. No `c=1` ancestor or `c=0` leaf occurs, so the special exceptional positive-input issue is absent. Every tested odd hub has `b > 4m+192q+40` and both costs are far below `15q=4410`.

A second independently written exact arithmetic traversal, based instead on Agent1's source-certified **power and mass inverse equations** `s=d+b/2+3=2^t*(c+3)`, `2k+c+2t+1+c%2=b+d`, produced **identical odd-hub counts**: 161,223 and 160,455. This separate implementation is available in the original invocation's local scratch environment; `verify.py` is the retained deterministic source-recursion checker.

## What these observations prove and what they do not

Source Lean `inverseAt_complete`, `positive_G_feeder`, `reachable_even_mod4`, `even_left_power_shape`, and Agent45's two-feeder reduction already rigorously justify the **type** of each finite proof obligation. The script checks the 643,357 leaf obligations and proves finite search termination at q=294 computationally. Combining its exact outcome with the source theorems is a plausible finite computer-aided argument for excluding the **single critical index n=4706**.

However, the search's full graph traversal, each terminal classification, and the final actual blank-entry `Reach` conclusion are **not Lean kernel-checked against the original source here**. A reader must independently trust or reproduce `verify.py` to treat this as a computer-assisted finite proof. Do not place a claimed blank-entry reachability exclusion in `results/` until a source-connected checker or compact independent mathematical certificate proves these facts.

Agent1 had earlier reported four finite q values (294, 498, 633, 774) that exceeded a 300,000-distinct-hub combined cap. This work resolves the finite enumeration for q=294 by raising the exact per-root exploration limit above the observed 161k/160k totals; q498 remains unresolved by this experiment after a 280,000-node cap **per root**. No all-q theorem or general P1 nonhalting claim follows.

## Reproduction

The script requires Python 3 standard library only, does not download data, and writes no files. It implements its own exact original-source inverse generator and power-of-14 classifier, prints counts and checks exceptional categories. There are no random choices. The `cap=1_000_000` default exceeds both q294 root cone sizes. Original local direct-source checker sha256 `bfdb0b47935a4d7b58e2aef37e8b964628dbee7642e9f68c4b8995a454b50ff2`; repository copy uses the same algorithm with presentation-only changes.
