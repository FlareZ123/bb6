# Agent 7: a sparse all-time blank-reachability portal at P1 right counter 3

**Status:** All-natural source-level Lean proof; P1 and BB(6) remain undecided. This is an intermediate result in `im-results/`.

Target raw 6-state 2-symbol machine:
`1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`.
The authentic blank-tape orbit enters the exact P1 accelerator at `(2,1)`. Original-machine semantics are established by upstream DeepMind Cryptids and the repository's Agent19 source bridge. The present theorem is about the unmodified `BB6.Agent1.Reach` definition.

## Mathematical result

For every natural `z>=1`, the real reachable set satisfies

```
Reach (8*z) 3 =>
  z=2 or exists j:Nat, 3*z+4=7*2^j.
```

Equivalently, by a proved mod-3 parity argument, `j` is even, so the sharpened theorem states:

```
Reach (8*z) 3 =>
  z=2 or exists m:Nat, 3*z+4=7*4^m.
```

The exception `z=2` arises only from the depth-zero positive-odd feeder and has not been shown genuinely reachable. The other possible `z` values form the extremely sparse sequence `1,8,36,148,...`. This is a **necessary** restriction, with no asserted sufficiency or machine halting conclusion.

## Proof structure

The full-source proof is `EightThree.lean` with named theorems `reachable_eightk_three_sparse` and `reachable_eightk_three_power_four`.

1. Agent50's exact `positive_G_feeder` converts any reachable `(8z,3)` into a true G inverse `(k,v)` with a previously reached `(2k-4,v+4)`. The exceptional `v=1` G input is globally excluded because `4z+6` has 2-adic valuation one.
2. Agent1's source-complete inverse iff (`ancestor_iff_power_mass`) requires `4z+6=2^t(v+3)` and `2k+v+2t+1+v%2=8z+3`. Divisibility by 4 excludes all `t>=2`.
3. At `t=0`, `v=4z+3` and the preceding left counter is `4z-6`. The proved blank-positive-even-left modulo-4 restriction leaves only `z=1` or `z=2`.
4. At `t=1`, `v=2z` and the predecessor is `(6z-4,2z+4)`. Agent1's global even-positive-right power shape gives `6z+8=14*2^j`, which is exactly `3z+4=7*2^j`. Modulo 3 forces `j` even.

All branch constraints use genuine blank-entry `Reach` and the exact original `GAncestor` definitions. The proof is unconditional over all z and all times, and uses no bounded simulation.

## Reproduction and status

Manual-only CI workflow `.github/workflows/agent7-p1-eight-three.yml` installs Lean `4.36.0-rc2`, compiles the **unmodified repository source chain** `GParity,GInverse,PosEvenForm,ResetGate,P1Triple,P1ResidualArithmetic,P1ResidualReach,P1FiniteInverse,P1InverseLog,MassInverse,InverseIff`, then compiles our new `EightThree.lean` and prints the final theorem's axioms. First run [41465203659](https://github.com/FlareZ123/bb6/actions/runs/41465203659) successfully verified the `2^j` statement at commit `53257509585e31fbac86b56cd4da721d7f6af359`. A second run will certify the additional power-of-four strengthening.

## Limitations and promising directions

This is a reusable structural restriction on the odd right-counter gateway, not a full P1 halting certificate. For the two difficult genuine critical-index sectors `n=2,14 (mod16)`, the target `(H(n)-6,3)` has first coordinate `4 mod8`, so the `0 mod8` portal addressed here does not directly settle those surviving classes.

Try deriving an analogous two-dimensional sparse-orbit grammar for `(8z+4,3)`, particularly the two exact positive feeder lines of Agent45's all-q critical iff. A stronger forward blank-reach invariant would be needed to close the surviving P1 halting basin.
