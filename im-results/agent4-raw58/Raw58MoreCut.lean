import Raw58Cut
import Raw58RDData
import Raw58LC1Data
import Raw58RE1Data
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent4Raw58MoreCut
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent50RootFrontier
open BB6.Agent50RecursiveResidual
open BB6.Agent31ThreeHole BB6.Agent10ZipAudit
abbrev parent : PartialMachine := BB6.Agent4Raw58Cut.parent
abbrev child (mv : Move) : PartialMachine := refine parent (0,true) (some mv)
def remaining : List Move := [⟨false,false,4⟩, ⟨false,false,5⟩, ⟨false,true,2⟩, ⟨false,true,5⟩, ⟨true,false,0⟩, ⟨true,false,1⟩, ⟨true,false,4⟩, ⟨true,false,5⟩, ⟨true,true,5⟩]
theorem remaining_count : remaining.length = 9 := by decide
theorem first_query : BB6.Agent50RecursiveResidual.queryOK 156 parent 7 (0,true) = true := by decide
theorem child_dichotomy (mv : Move) (m : Machine) (hm : compatible (child mv) m) :
    WeightedBound 156 m ∨ mv ∈ remaining := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  · left; intro k d hk hd
    exact Nat.le_trans (BB6.Agent4Raw58Cut.cycle0.sound m hm k d hk hd) (by decide)
  · left; intro k d hk hd
    exact Nat.le_trans (BB6.Agent4Raw58Cut.cycle6.sound m hm k d hk hd) (by decide)
  · right; decide
  · left; intro k d hk hd
    exact Nat.le_trans (BB6.Agent4Raw58Cut.cycle18.sound m hm k d hk hd) (by decide)
  · left; intro k d hk hd
    exact Nat.le_trans (BB6.Agent4Raw58Cut.cycle1.sound m hm k d hk hd) (by decide)
  · left; intro k d hk hd
    exact Nat.le_trans (BB6.Agent4Raw58Cut.cycle7.sound m hm k d hk hd) (by decide)
  · right; decide
  · left; intro k d hk hd
    exact Nat.le_trans (BB6.Agent4Raw58Cut.cycle19.sound m hm k d hk hd) (by decide)
  · left; intro k d hk hd
    exact Nat.le_trans (BB6.Agent4Raw58Cut.cycle2.sound m hm k d hk hd) (by decide)
  · right; decide
  · left; intro k d hk hd
    exact Nat.le_trans (BB6.Agent4Raw58LC1.certificate.sound m hm k d hk hd) (by decide)
  · left; intro k d hk hd
    exact Nat.le_trans (BB6.Agent4Raw58Cut.cycle20.sound m hm k d hk hd) (by decide)
  · left; intro k d hk hd
    exact Nat.le_trans (BB6.Agent4Raw58Cut.cycle3.sound m hm k d hk hd) (by decide)
  · left; intro k d hk hd
    exact Nat.le_trans (BB6.Agent4Raw58RD.certificate.sound m hm k d hk hd) (by decide)
  · left; intro k d hk hd
    exact Nat.le_trans (BB6.Agent4Raw58Cut.cycle15.sound m hm k d hk hd) (by decide)
  · left; intro k d hk hd
    exact Nat.le_trans (BB6.Agent4Raw58Cut.cycle21.sound m hm k d hk hd) (by decide)
  · right; decide
  · left; intro k d hk hd
    exact Nat.le_trans (BB6.Agent4Raw58RE.certificate.sound m hm k d hk hd) (by decide)
  · right; decide
  · left; intro k d hk hd
    exact Nat.le_trans (BB6.Agent4Raw58RE1.certificate.sound m hm k d hk hd) (by decide)
  · right; decide
  · right; decide
  · right; decide
  · right; decide
theorem parent_dichotomy (m : Machine) (hm : compatible parent m) :
    WeightedBound 156 m ∨ ∃ mv ∈ remaining, compatible (child mv) m := by
  cases hs : m (0,true) with
  | none =>
    exact Or.inl (BB6.Agent50RecursiveResidual.queryOK_sound 156 parent 7 (0,true)
      first_query m (compatible_refine hm (0,true) none hs))
  | some mv =>
    have hc := compatible_refine hm (0,true) (some mv) hs
    rcases child_dichotomy mv m hc with hb | hr
    · exact Or.inl hb
    · exact Or.inr ⟨mv,hr,hc⟩
#print axioms parent_dichotomy
end BB6.Agent4Raw58MoreCut
