import ChampionRootBridge

namespace BB6Coverage.Agent8M2EvenResidueZero

open BB6Coverage.Agent48Champion

/-- Finite 44-step setup kernel for the m=2, n=8*k residue-zero bridge.
The start word on [-13,0] is 11111111110010. -/
def m2ZeroSetupStart : FConfig :=
  ⟨3, 0, [-13,-12,-11,-10,-9,-8,-7,-6,-5,-4,-1]⟩

/-- The setup writes 01111111111111 on [-13,0] and stops at -14. -/
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

/-- Finite 14-step postlude kernel: thirteen ones followed by a zero. -/
def m2ZeroPostludeStart : FConfig :=
  ⟨1, 0, (List.range 13).map Int.ofNat⟩

/-- The postlude writes 00100100100101 and stops in E at head 14. -/
def m2ZeroPostludeEnd : FConfig :=
  ⟨4, 14, [13,11,8,5,2]⟩

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

#print axioms m2ZeroSetup_exact
#print axioms m2ZeroSetup_heads
#print axioms m2ZeroPostlude_exact
#print axioms m2ZeroPostlude_heads

end BB6Coverage.Agent8M2EvenResidueZero
