# P1 L1 all-parameter first-positive-reset obstruction (Agent 50)

## Verified theorem

For every natural `q ≥ 1`, let `u = 7*2^(16*q)-4*q-3` and let the exact authentic critical feeder `L1=(6*u-2,2*u+5)`. Suppose `t ≥ 1`, `k ≥ 2`, `c` odd, and original `BB6.Agent47P1.inverseAt (6*u-2) (2*u+5) t = some (k,c)`. For any arbitrary-length authenticated `BB6.Agent1UpperTail.UpperTail (2*k-4) (c+4) (t+1) b d m n` (a chain of depth-zero odd inverse steps), the affine halting wall `b=4*m+64*q+16` is impossible.

This is `BB6.Agent50L1OneReset.l1_first_reset_no_wall` in [L1OneResetBridge.lean](./L1OneResetBridge.lean). The pure parameter-uniform dyadic contradiction is [L1OneResetArithmetic.lean](./L1OneResetArithmetic.lean), theorem `no_one_reset_l1_budget`.

**Original-source kernel verification:** Manual unmodified-source Lean 4.36.0-rc2 [GitHub Actions run 41577652633](https://github.com/FlareZ123/bb6/actions/runs/41577652633), job `source-certify`, **SUCCESS**, checked at commit `598a76aa8ff8ee73cb2116801d1525c9eecf1160`. Compiler `#print axioms` for both final theorems reports `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. The manual-only workflow `.github/workflows/agent1-p1-quarter.yml` compiles unmodified original `GParity/GInverse/P1FiniteInverse/MassInverse/OddConeMass/UpperTail/P1TwoRoot/RootWallArithmetic/P1InverseLog` and then the two new modules. A previous failing job 41577435372 detected a source hypothesis requiring `4≤b` rather than the local mock's `8≤b`; the source call was corrected, and the successful run directly eliminated that mock discrepancy.

## Mathematical mechanism

Write `P=2^(16*q)`. For the exact L1 first inverse, source power is `2^t*(c+3)+20*q+8=35*P`; hence `t≤16*q` and `2^t∣(20*q+8)`. Defining `p0=2^(16*q-t)`, `r=(20*q+8)/2^t`, `B=2*k+8`, and `K=32*q+12+2*t-r`, source odd-inverse mass gives

```
B + K + 35*p0 = 56*P,
0 < K ≤ 64*q+12.
```

If the following depth-zero tail hits the affine wall, source tail exactness yields `B=2^n*(4*(t+1+n)+64*q+28)`. The dyadic-divisibility difference `B+K ≡ 0 (mod p0)` with `0<K<p0` then forces `n < 16*q-t` and `2^n≤K≤76*q`, so `B≤17024*q²`. The mass identity forces `B+K≥38*P`, which contradicts the source-verified growth `65536*q²≤P`.

## Scope and remaining work

This **rules out exactly a first positive-depth L1 reset followed by any number of depth-zero steps**, without assuming finite inverse cone length or q residue class. The existing Agent 1 [L0OneResetBridge](../agent1-p1-quarter/L0OneResetBridge.lean) source proof is the L0 counterpart, while L1 can also contain a nonempty upper prefix *before* its first positive-depth reset. The current theorem does **not** exclude such prefix-reset-suffix paths, histories with two or more positive-depth inversions, the exceptional c=1 branch, the n≡14(mod16) sector, or the exponentially expensive alternative in Agent 9's full reachability dichotomy. It does not determine whether P1 halts or the value of BB(6).

A separate unfinished stronger local investigation tests an arbitrary upper prefix. Its arithmetic lemma is not part of this source-verified theorem and should never be cited as an unconditional P1 decision.
