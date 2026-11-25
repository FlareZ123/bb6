import RecursiveResidual
import Raw57Easy
import Raw57RAData
import Raw57RB0Data
import Raw57RC0Data
import Raw57RB1Data
import Raw57RC1Data
import Raw57RE1Data
import Raw57RF0Data
import Raw57RE0Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent6Raw57Cut
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent50RootFrontier
open BB6.Agent50RecursiveResidual

abbrev parent : PartialMachine := BB6.Agent6Raw57Easy.p57
abbrev child (mv : Move) : PartialMachine := refine parent (0,true) (some mv)
def remaining : List Move := [⟨true,false,0⟩, ⟨true,true,0⟩, ⟨false,false,1⟩, ⟨true,false,1⟩, ⟨false,false,2⟩, ⟨true,false,2⟩, ⟨false,false,3⟩, ⟨true,false,4⟩, ⟨false,false,5⟩, ⟨true,false,5⟩, ⟨true,true,5⟩]
theorem remaining_count : remaining.length = 11 := by decide
theorem first_query : BB6.Agent50RecursiveResidual.queryOK 273 parent 7 (0,true) = true := by decide

theorem child_dichotomy (mv : Move) (m : Machine) (hm : compatible (child mv) m) :
    WeightedBound 273 m ∨ mv ∈ remaining := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  · left
    intro k d hk hd
    exact Nat.le_trans (BB6.Agent6Raw57Easy.la.sound m hm k d hk hd) (by decide)
  · left
    intro k d hk hd
    exact Nat.le_trans (BB6.Agent6Raw57RA.certificate.sound m hm k d hk hd) (by decide)
  · right; decide
  · right; decide
  · right; decide
  · left
    intro k d hk hd
    exact Nat.le_trans (BB6.Agent6Raw57RB0.certificate.sound m hm k d hk hd) (by decide)
  · right; decide
  · left
    intro k d hk hd
    exact Nat.le_trans (BB6.Agent6Raw57RB1.certificate.sound m hm k d hk hd) (by decide)
  · right; decide
  · left
    intro k d hk hd
    exact Nat.le_trans (BB6.Agent6Raw57RC0.certificate.sound m hm k d hk hd) (by decide)
  · right; decide
  · left
    intro k d hk hd
    exact Nat.le_trans (BB6.Agent6Raw57RC1.certificate.sound m hm k d hk hd) (by decide)
  · right; decide
  · left
    intro k d hk hd
    exact Nat.le_trans (BB6.Agent6Raw57Easy.rd.sound m hm k d hk hd) (by decide)
  · left
    intro k d hk hd
    exact Nat.le_trans (BB6.Agent6Raw57Easy.ld1.sound m hm k d hk hd) (by decide)
  · left
    intro k d hk hd
    exact Nat.le_trans (BB6.Agent6Raw57Easy.rd1.sound m hm k d hk hd) (by decide)
  · left
    intro k d hk hd
    exact Nat.le_trans (BB6.Agent6Raw57Easy.le.sound m hm k d hk hd) (by decide)
  · left
    intro k d hk hd
    exact Nat.le_trans (BB6.Agent6Raw57RE0.certificate.sound m hm k d hk hd) (by decide)
  · right; decide
  · left
    intro k d hk hd
    exact Nat.le_trans (BB6.Agent6Raw57RE1.certificate.sound m hm k d hk hd) (by decide)
  · right; decide
  · left
    intro k d hk hd
    exact Nat.le_trans (BB6.Agent6Raw57RF0.certificate.sound m hm k d hk hd) (by decide)
  · right; decide
  · right; decide

/-- Partial closure of the six-hole raw57 cylinder, including the actual halt branch. -/
theorem parent_dichotomy (m : Machine) (hm : compatible parent m) :
    WeightedBound 273 m ∨ ∃ mv ∈ remaining, compatible (child mv) m := by
  cases hs : m (0,true) with
  | none =>
    exact Or.inl (BB6.Agent50RecursiveResidual.queryOK_sound 273 parent 7 (0,true)
      first_query m (compatible_refine hm (0,true) none hs))
  | some mv =>
    have hc := compatible_refine hm (0,true) (some mv) hs
    rcases child_dichotomy mv m hc with hb | hr
    · exact Or.inl hb
    · exact Or.inr ⟨mv,hr,hc⟩

theorem parent_dichotomy395 (m : Machine) (hm : compatible parent m) :
    WeightedBound 395 m ∨ ∃ mv ∈ remaining, compatible (child mv) m := by
  rcases parent_dichotomy m hm with h | h
  · left; intro k d hk hd; exact Nat.le_trans (h k d hk hd) (by decide)
  · exact Or.inr h

#print axioms parent_dichotomy395
end BB6.Agent6Raw57Cut
