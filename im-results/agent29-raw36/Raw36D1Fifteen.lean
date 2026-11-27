import Raw36D1SymmetryCut

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent29Raw36
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent47PartialAudit

/-- Five B1 choices are certified finite translated cycles, directly from
    the first-hole partial audit used in the eight-hole Raw36 cut. -/
def b1Cycles : List Move :=
  [⟨false,false,2⟩,
   ⟨false,false,3⟩,
   ⟨true,false,3⟩,
   ⟨true,true,1⟩,
   ⟨true,true,3⟩]

/-- The exact fifteen nontrivial first-hole choices once those five
    cycles and the four E/F relabeling aliases are removed. -/
def b1Retained : List Move :=
  [⟨false,false,0⟩,
   ⟨false,false,1⟩,
   ⟨false,false,4⟩,
   ⟨false,true,0⟩,
   ⟨false,true,1⟩,
   ⟨false,true,2⟩,
   ⟨false,true,3⟩,
   ⟨false,true,4⟩,
   ⟨true,false,0⟩,
   ⟨true,false,1⟩,
   ⟨true,false,2⟩,
   ⟨true,false,4⟩,
   ⟨true,true,0⟩,
   ⟨true,true,2⟩,
   ⟨true,true,4⟩]

theorem b1Retained_count : b1Retained.length = 15 := by decide
theorem b1Retained_nodup : b1Retained.Nodup := by decide
theorem b1Cycles_count : b1Cycles.length = 5 := by decide

theorem b1Moves_partition (mv : Move) :
    mv ∈ b1Retained ∨
      (mv.next = 5 ∧ ⟨mv.write,mv.right,4⟩ ∈ b1Retained) ∨
      mv ∈ b1Cycles := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cases w <;> cases r <;> decide

/-- Each cycle branch uses its original exact FiniteCycle witness, while
    all other physical transitions remain explicit open leaf conditions. -/
def b1Kids (mv : Move) : PartialAudit :=
  if mv = ⟨false,false,2⟩ then .closed (.cycle 8 1 false (0)) else
  if mv = ⟨false,false,3⟩ then .closed (.cycle 7 1 false (-1)) else
  if mv = ⟨true,false,3⟩ then .closed (.cycle 7 1 false (-1)) else
  if mv = ⟨true,true,1⟩ then .closed (.cycle 1 7 true (0)) else
  if mv = ⟨true,true,3⟩ then .closed (.cycle 5 2 true (0)) else
  .unresolved

def b1Audit : PartialAudit := .split 6 (1,true) b1Kids
theorem b1Audit_checked : partialCheck 162 d1 b1Audit = true := by decide

theorem b1Kids_cycle_empty (mv : Move) (h : mv ∈ b1Cycles) :
    partialResiduals (b1Child mv) (b1Kids mv) = [] := by
  simp only [b1Cycles, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl
  all_goals rfl

theorem b1Kids_open (mv : Move) (h : mv ∉ b1Cycles) :
    b1Kids mv = .unresolved := by
  have hn0 : mv ≠ (⟨false,false,2⟩ : Move) := by
    intro heq
    apply h
    simp [b1Cycles, heq]
  have hn1 : mv ≠ (⟨false,false,3⟩ : Move) := by
    intro heq
    apply h
    simp [b1Cycles, heq]
  have hn2 : mv ≠ (⟨true,false,3⟩ : Move) := by
    intro heq
    apply h
    simp [b1Cycles, heq]
  have hn3 : mv ≠ (⟨true,true,1⟩ : Move) := by
    intro heq
    apply h
    simp [b1Cycles, heq]
  have hn4 : mv ≠ (⟨true,true,3⟩ : Move) := by
    intro heq
    apply h
    simp [b1Cycles, heq]
  simp [b1Kids, hn0, hn1, hn2, hn3, hn4]

/-- Source-exact 15-case criterion for the full seven-hole D1=1LB
    cylinder. This includes the genuine halt choice and all 24 ordinary
    B1 moves; no completeness assumption is hidden in the census. -/
theorem d1_bound_from_fifteen (B : Nat) (hB : 162 ≤ B)
    (h : ∀ mv ∈ b1Retained, ∀ m,
      compatible (b1Child mv) m → WeightedBound B m)
    (m : Machine) (hm : compatible d1 m) : WeightedBound B m := by
  rcases partialSound 162 d1 b1Audit d1_root d1_nohalt
    b1Audit_checked m hm with hb | ⟨e,he,hh⟩
  · intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) hB
  · rw [partialResiduals.eq_3] at he
    obtain ⟨mv,_,hmem⟩ := List.mem_flatMap.mp he
    have hno : mv ∉ b1Cycles := by
      intro hc
      rw [b1Kids_cycle_empty mv hc] at hmem
      simp at hmem
    rw [b1Kids_open mv hno, partialResiduals.eq_1] at hmem
    obtain ⟨e',he',heq⟩ := List.mem_map.mp hmem
    have he'' : e' = ([], b1Child mv) := by
      simpa only [List.mem_singleton] using he'
    rw [← heq,he''] at hh
    rcases b1Moves_partition mv with hs | ⟨hq,hs⟩ | hc
    · exact h mv hs m hh
    · rcases mv with ⟨w,r,q⟩
      change q = 5 at hq
      subst q
      exact b1F_bound B w r (h _ hs) m hh
    · exact False.elim (hno hc)

/-- Ready for any set of original-source certificates proving exactly
    the fifteen retained child Covers at B>=162 (candidate B=166). -/
theorem d1_cover_from_fifteen (B : Nat) (hB : 162 ≤ B)
    (h : ∀ mv ∈ b1Retained, Cover (WeightedBound B) (b1Child mv)) :
    Cover (WeightedBound B) d1 := by
  apply Cover.leaf
  intro m hm
  exact d1_bound_from_fifteen B hB
    (by intro mv hmv m hc; exact (h mv hmv).sound m hc) m hm

#print axioms b1Audit_checked
#print axioms b1Kids_cycle_empty
#print axioms b1Moves_partition
#print axioms d1_bound_from_fifteen
#print axioms d1_cover_from_fifteen
end BB6.Agent29Raw36
