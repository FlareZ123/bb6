import Raw124ZeroLFTrivial
import RecursiveResidual
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent12Raw124ZeroLFParent
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent12Raw124ZeroLFTrivial
open BB6.Agent31ThreeHole
abbrev parent : PartialMachine := pBranch
abbrev child (mv : Move) : PartialMachine := refine parent (5,false) (some mv)
def remaining : List Move := [⟨false,false,4⟩,⟨false,true,0⟩,⟨false,true,1⟩,⟨false,true,4⟩,⟨true,false,0⟩,⟨true,false,1⟩,⟨true,false,2⟩,⟨true,false,4⟩,⟨true,true,0⟩,⟨true,true,1⟩,⟨true,true,2⟩,⟨true,true,4⟩]
theorem remaining_count : remaining.length = 12 := by decide

theorem first_query : BB6.Agent50RecursiveResidual.queryOK 15 parent 9 (5,false) = true := by decide

theorem weighted_mono {B C : Nat} {m : Machine} (h : B ≤ C) (hb : WeightedBound B m) : WeightedBound C m :=
  fun k d hk hd => Nat.le_trans (hb k d hk hd) h

theorem child_dichotomy (mv : Move) (m : Machine) (hm : compatible (child mv) m) :
    NeverHalts m ∨ mv ∈ remaining := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  · exact Or.inl (never0LA m hm)
  · right; decide
  · right; decide
  · right; decide
  · exact Or.inl (never0LB m hm)
  · right; decide
  · right; decide
  · right; decide
  · exact Or.inl (never0LC m hm)
  · exact Or.inl (never0RC m hm)
  · right; decide
  · right; decide
  · exact Or.inl (never0LD m hm)
  · exact Or.inl (never0RD m hm)
  · exact Or.inl (never1LD m hm)
  · exact Or.inl (never1RD m hm)
  · right; decide
  · right; decide
  · right; decide
  · right; decide
  · exact Or.inl (never0LF m hm)
  · exact Or.inl (never0RF m hm)
  · exact Or.inl (never1LF m hm)
  · exact Or.inl (never1RF m hm)

/-- The 25-way F0 partition, retaining exactly the 12 nontrivial ordinary children. -/
theorem parent_dichotomy (m : Machine) (hm : compatible parent m) :
    WeightedBound 15 m ∨ ∃ mv ∈ remaining, compatible (child mv) m := by
  cases hs : m (5,false) with
  | none => exact Or.inl (BB6.Agent50RecursiveResidual.queryOK_sound 15 parent 9 (5,false)
      first_query m (BB6.Agent50RecursiveResidual.compatible_refine hm (5,false) none hs))
  | some mv =>
    have hc := BB6.Agent50RecursiveResidual.compatible_refine hm (5,false) (some mv) hs
    rcases child_dichotomy mv m hc with hn | hr
    · exact Or.inl (weighted_never 15 m hn)
    · exact Or.inr ⟨mv,hr,hc⟩

/-- Semantic integration of all residual children, without rerunning their internal audits. -/
theorem cover_of_children (B : Nat) (hB : 15 ≤ B)
    (hc : ∀ mv ∈ remaining, Cover (WeightedBound B) (child mv)) :
    Cover (WeightedBound B) parent := by
  apply Cover.leaf
  intro m hm
  rcases parent_dichotomy m hm with h | ⟨mv,hmv,hc'⟩
  · exact weighted_mono hB h
  · exact (hc mv hmv).sound m hc'

/-- A checked exact table transport permits any independently proved child bound. -/
theorem transport {q : PartialMachine} {mv : Move} {B C : Nat}
    (he : tableOK (child mv) q = true) (hle : B ≤ C)
    (hb : ∀ m, compatible q m → WeightedBound B m) : Cover (WeightedBound C) (child mv) := by
  apply Cover.leaf
  intro m hm
  have h := tableOK_sound _ _ he
  exact weighted_mono hle (hb m (h ▸ hm))

#print axioms parent_dichotomy
#print axioms cover_of_children
#print axioms transport
end BB6.Agent12Raw124ZeroLFParent
