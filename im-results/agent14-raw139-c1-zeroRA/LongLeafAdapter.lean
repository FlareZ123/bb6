import FastThreeHoleAudit
import CrossCoverage

namespace BB6.Agent14C1ZeroRALong
open BB6Coverage BB6.Agent13BlankDelay BB6.CoverageAdapter

def p : PartialMachine := FAR.fromCodes [7,17,11,23,14,1,3,16,12,11,24,3]
def m0 : Machine := fun s => (p s).getD none

theorem other_fixed : ∀ s : Slot, s ≠ (5,false) → p s = some (m0 s) := by
  rintro ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> cases b <;> decide

theorem other_live : ∀ s : Slot, s ≠ (5,false) → (m0 s).isSome = true := by
  rintro ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> cases b <;> decide

theorem hole_halts : m0 (5,false) = none := by decide

/-- An exact halt of the halted completion decides the entire one-hole
    cylinder: all 24 ordinary completions are total and never halt. -/
theorem long_cover (h : BB6.Coverage.HaltsAt
    (BB6.Coverage.tick (toAgent13Machine m0)) 14876965) :
    Cover (WeightedBound 14876970) p := by
  apply Cover.leaf
  intro m hm
  cases hh : m (5,false) with
  | none =>
    have eq : m = m0 := by
      funext s
      by_cases hs : s = (5,false)
      · rw [hs,hh,hole_halts]
      · exact hm s (m0 s) (other_fixed s hs)
    subst m
    have ht : HaltsAfter m0 14876964 := by
      have ht := (halts_agree (toAgent13Machine m0) 14876964).mp h
      simpa only [toAgent8_toAgent13] using ht
    intro k d hk hd
    have he := halting_time_unique m0 k 14876964 hk ht
    have hd' : d < 6 := List.mem_range.mp (List.mem_filter.mp hd).1
    omega
  | some mv =>
    apply weighted_never _ _ (all_ordinary_never m ?_)
    intro s
    by_cases hs : s = (5,false)
    · exact ⟨mv, hs ▸ hh⟩
    · rw [hm s (m0 s) (other_fixed s hs)]
      exact Option.isSome_iff_exists.mp (other_live s hs)

#print axioms long_cover
end BB6.Agent14C1ZeroRALong
