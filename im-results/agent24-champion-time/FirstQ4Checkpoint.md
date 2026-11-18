# Positive-z first q4 checkpoint: two S0 drains around Rst1'

**Status (18 November 2026):** the complete primitive-transition decomposition has been tested on 30 parameter cases. The source-level composition through the second S0 drain is drafted in Lean. The final postlude has an exact ten-step finite bridge and frame-lifting theorem. The full postlude composition and accepted CI import closure are not yet complete. This is an intermediate lower-bound continuation, not a BB(6) solution or a halting witness.

## Exact phase decomposition

Let
`D(n)=drainCost n 0`, and start from the marker-1 S0 configuration
```lean
s0Config (markerWord 1 ++ d0 ++ d1pow L ++ lh) A z 0 0
```
with `A≥1`, `0≤z<2^A`, and the relevant source-family restrictions on `L`.

The raw TM2 execution has the following exact endpoint factorization:

1. **General S0 drain:** `D(z)` steps, ending at
   `s0Config l0 A 0 z 0`.
2. **Existing Rst1' macro:** `97+12*(L+A)+3*z` steps, ending at
   `s1Config (L+A+2) (2^(L+A+2)-2^A-1) 2 z (2^z-1) 0 (3*z+5)`.
3. **All-ones S0 drain:** `D(2^z-1)` steps, ending at
   `s0Config l2 z 0 (2^z-1) (3*z+5)`.
4. **First-q4 postlude:** `9*z+10` steps, ending at state 4, head 1, with the first q4 checkpoint tape.

Thus the total time to the first q4 checkpoint is
[
T=D(z)+D(2^z-1)+12(A+L+z)+107.
]

## The setup bridge is already Rst1'

The first drain output is definitionally the S1 input
```lean
s1Config L 0 1 A 0 z 0.
```
The existing theorem `BB6Coverage.Agent8Rst1PrimeTail.rst1Prime_counted_macro L A z 0`
has exactly the required cost `97+12*(L+A)+3*z` and returns the S1 successor above. By the definition of `s1Config`, that successor is an S0 configuration with left context
```lean
l2 = markerWord 2 ++ d0 ++
  binDec (L+A+2) (2^(L+A+2)-2^A-1) ++ lh.
```
This is exactly the input required by the second S0 drain. The explicit head-facing word is
```
110 ++ (100)^(A+1) ++ 111 ++ (100)^(L+1) ++ 1110111.
```
Consequently **no new pre-bridge macro is needed**: use the existing Rst1' source theorem. The S0 drain module provides the general first drain and all-ones second drain.

## The new postlude is a sweep plus a fixed bridge

At the second-drain output, the machine is in state 3 at head `h2=3*z+5`. Its left-facing word begins with `d1pow z`, and its right cell `h2+1` is zero.

Apply `counted_left_sweep (3*z)` (equivalently Agent 48's `state3_left_ones_scan (3*z)`). This costs `9*z` and returns to state 3 at head 5. The seven-cell window at offsets `[-5,1]` is then exactly `0010110`.

The remaining ten transitions are the fixed finite trace
```lean
firstQ4PostludeStart : FConfig := ⟨3, 0, [-3, -1, 0]⟩
firstQ4PostludeEnd   : FConfig := ⟨4, -4, [-5, 0, 1]⟩

fRun tm2 10 firstQ4PostludeStart = some firstQ4PostludeEnd
```
The output window is `1000011`; its head is 1 and state is 4. The long right unary block beginning at `h2+7=3*z+12` is preserved by the sweep and bridge. The bridge is frame-lifted in `FirstQ4PostludeBridge.lean`.

The final left-facing q4 word is
```
011 ++ binDec (A+L+2) (M-1) ++ lh
```
where `M=2^A*(2^(L+2)-1)`. Its identity with the `l2.drop 4` tail follows from
```lean
binDec (A+L+2) (M-1) = d0pow A ++ d1 ++ d0pow (L+1).
```

## Reproducible raw-step evidence

`verify_marker1_s0_two_drain_checkpoint.cjs` executes the original six-state TM2 transition table one primitive step at a time. It compares the complete finite one-support of the tape at the first drain endpoint, Rst1' endpoint, second drain endpoint, and final q4 checkpoint. It also checks the q4/read-zero event count and the fixed postlude bridge windows.

Tested:
- `(A,L)=(4,2)`, `z=0..9`;
- `(A,L)=(3,2)`, `z=0..5`;
- `(A,L)=(5,4)`, `z=0..5`;
- `(A,L,z)=(5,4,7),(6,4,7),(7,4,7),(5,6,7),(5,4,9),(6,4,9),(7,4,9),(5,6,9)`.

**30 cases, 8,970,870 primitive transitions, zero failures.** The postlude is separately checked as `9*z` sweep steps with bridge input `0010110`, followed by ten steps with output `1000011`.

The Rst1' left-context list identity was additionally checked for all 156 pairs `1≤A≤12`, `0≤L≤12`, with zero failures. These are computational checks; the Lean source proofs remain the acceptance criterion.

## Lean artifacts and remaining work

- `FirstQ4CheckpointPrePostlude.lean`: source-draft composition of the general S0 drain, existing Rst1' macro, and all-ones S0 drain.
- `FirstQ4PostludeBridge.lean`: exact ten-step finite trace, head-window containment, and arbitrary-tape frame lift.
- `CountedLBinDecHRun.lean`: repair work on the H-run dependency used by `S0CountedDrain`; the latest CI run still needs to be checked after the most recent fixes.
- `verify_marker1_s0_two_drain_checkpoint.cjs`: complete primitive-step regression.

Remaining:
1. Get `CountedLBinDecHRun.lean` and its dependency chain to compile without `sorryAx`.
2. Compile `S0CountedDrain.lean`, `Rst1PrimeBridge6Source.lean`, `FirstQ4CheckpointPrePostlude.lean`, and `FirstQ4PostludeBridge.lean` in one exact Lean import closure.
3. Prove the sweep-to-window match and identify the final frame with the canonical first q4 checkpoint.
4. Continue the positive-z nested q4 cycles and terminal behavior. The first checkpoint does not resolve those later cycles, nor does it supply a universal BB(6) upper bound.
