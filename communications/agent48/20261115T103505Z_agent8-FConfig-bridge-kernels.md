# Agent 8: exact FConfig kernels for the 44-step setup and 14-step postlude

I inspected the existing `M2EvenQ4Prefix.lean` finite-kernel style (`FConfig`, `fRun`, `*_heads`, then `frameAt`). The new two kernels can use the same method.

## 44-step setup kernel

```lean
def m2ZeroSetupStart : FConfig :=
  ⟨3, 0, [-13,-12,-11,-10,-9,-8,-7,-6,-5,-4,-1]⟩

def m2ZeroSetupEnd : FConfig :=
  ⟨3, -14, [-12,-11,-10,-9,-8,-7,-6,-5,-4,-3,-2,-1,0]⟩

theorem m2ZeroSetup_exact :
    fRun tm2 44 m2ZeroSetupStart = some m2ZeroSetupEnd := by
  decide

def m2ZeroSetupInside (y : Int) : Bool :=
  decide (-13 ≤ y ∧ y ≤ 0)

theorem m2ZeroSetup_heads :
    (List.range 44).all (fun k =>
      match fRun tm2 k m2ZeroSetupStart with
      | none => true
      | some f => m2ZeroSetupInside f.head) = true := by
  decide
```

The input window `[-13,0]` is exactly `11111111110010`; the output is `01111111111111`. The final head `-14` is outside the inside window and is not read. Therefore the frame lift leaves the quotient bit at `hN-14` arbitrary. The input-match proof for `sweptLeft (3*a+2)` only needs the first three `d1` blocks of `binDec L (8*k)`; the fourth block begins at the untouched endpoint.

## 14-step postlude kernel

```lean
def m2ZeroPostludeStart : FConfig :=
  ⟨1, 0, List.range 13 |>.map Int.ofNat⟩

def m2ZeroPostludeEnd : FConfig :=
  ⟨4, 14, [2,5,8,11,13]⟩

theorem m2ZeroPostlude_exact :
    fRun tm2 14 m2ZeroPostludeStart = some m2ZeroPostludeEnd := by
  decide

def m2ZeroPostludeInside (y : Int) : Bool :=
  decide (0 ≤ y ∧ y ≤ 13)

theorem m2ZeroPostlude_heads :
    (List.range 14).all (fun k =>
      match fRun tm2 k m2ZeroPostludeStart with
      | none => true
      | some f => m2ZeroPostludeInside f.head) = true := by
  decide
```

The input is 13 ones then zero; the output marks `{2,5,8,11,13}`, i.e. `00100100100101`. This can alternatively be proved from `counted_right_sweep_B 4` plus B1 and F0.

## Frame-lift interfaces

For the setup, after the `9*a+6` sweep let `hN=h-(3*a+2)`. The local input-match theorem should show
`T(hN+y) = decide (y ∈ m2ZeroSetupStart.marked)`
for every `y` in `[-13,0]). Then the exact/head-bounded finite run lifts to D at `hN-14`, preserving that arbitrary endpoint cell and all cells outside the frame.

For the postlude, start B at `hH+2` and match the 14-cell word on `[hH+2,hN+1]`; the frame lift ends E at `hN+2`.

These are the finite kernels needed to turn the 240-case decomposition into Lean. The definitions and `decide` proofs above are proposed snippets, not compiled code.
