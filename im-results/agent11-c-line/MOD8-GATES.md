# Agent 11: second infinite modular exclusion for Machine C

**Formal intermediate theorem, not a busy-beaver solution or holdout decision.** The target six-state machine is `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC`, whose published [Cryptids](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC.lean) acceleration starts from the actual blank entry `(5,0,1)`. The local transition definition is copied, with the upstream machine-to-map bridge remaining external.

## Main all-natural theorem

`BB6CLine.reset_mod8_four_unreachable`:

```text
for all j, j % 8 = 4 -> not Reach(2*j+1,3*j+4,0)
```

The theorem is **Lean 4.36.0-rc2 kernel checked**, all finite times and natural parameters, without sorry or nonstandard axioms.

Earlier `PARITY-GATES.md` excludes all reset indices `j%4=1` and all odd side-gateway indices, using global high-sector parity and the unique three-step reset predecessor chain.

The stronger `BB6CLine.stops_iff_mod8_gates` theorem now proves the **exact** remaining blank-entry accelerator stopping condition:

```text
eventual stopping
  iff
(∃ j>=1, j%4 != 1, j%8 != 4 and Reach(2*j+1,3*j+4,0))
or
(∃ n>=1, Reach(0,4*n,24*n+23)).
```

This excludes reset residues 1, 4, and 5 modulo 8, leaving residues 0, 2, 3, 6, 7. These remaining infinite classes are open, as is the side family.

## Proof method

The backward proof uses no finite search cutoff:

1. Every reachable `(a,k,0)` with `k>=6` has a reached ancestor `(a+k-5,2,k-2)`. The proof first follows the unique inverse steps through right counters 1, 3, and 4, then follows the entire high-counter sweep backward until middle counter 2.
2. For an odd `k>=6` with `(a+k)%4=2`, this reached ancestor contradicts the previously proved global parity invariant: its middle counter is even, its right counter is odd, and `(a+k-5+2)%4=3`. This excludes an infinite arithmetic family of low-counter resets.
3. The small `k=3`, `a%4=3` case is separately ruled out. A reached state `(a,3,0)` must come from `(a,2,1)`, which for `a%4=3` can only come from `(a,0,3)). A universal transition case split proves no successful accelerator transition ever outputs `(a,0,3)`.
4. Starting with any reachable `(a,k,0)` satisfying `a%8=1, k%8=0, k>=8`, its middle-two ancestor must come from the high branch rather than a zero-left even branch (the latter outputs first counter 2 mod4). Its prior middle-one ancestor cannot come from another high branch because that would create a reached even-first, middle-zero state. It therefore forces a previous reset `(a+k-2, (k-2)/2, 0)`. This reset has first counter 3 mod4, middle counter 3 mod4, and sum 2 mod4, contradicting steps 2 or 3.
5. Every reset gateway with `j%8=4` has precisely those input residues `a=2j+1, k=3j+4`, yielding the theorem.

All steps are explicitly machine-checked, including arbitrary large parameters and the two natural subtraction boundary cases.

## Verification and preservation

The complete sources `MoreResidue.lean` (7264 bytes, SHA-256 `dc6fe87cbf6c3b185997c5b5d7369e9c8a89bcf19729fbcf1f1ad876bfd7d475`) and `FinalGate.lean` (834 bytes, SHA-256 `515d7e918642c93f16d70fc6e88cd9db626923b906eac6b7c83461331113d2a2`) are losslessly stored in `mod8-lean.tar.xz.b64`. Run `python reconstruct-mod8.py` (requires `filelock`) for checksum-verifying, locked atomic reconstruction.

First reconstruct previous modules with `python reconstruct.py` and `python reconstruct-parity.py`. Compile Lean modules to `.olean` in order: `CLine, LowGate, BackGate, ResetGate, CParity, CParityGates, MoreResidue`; finally compile `FinalGate.lean`. All imports use local source modules plus Lean's bundled `Std`, no Mathlib. The final `#print axioms` result is `[propext, Classical.choice, Quot.sound]`, and all proof files compile without `sorryAx` or `native_decide`.

**Important limitation:** The surviving infinite families remain unresolved. This result narrows the actual blank-tape reachability problem and supplies general-purpose backward packet analysis, but it does not establish nonhalting, halting, or a value of BB(6).
