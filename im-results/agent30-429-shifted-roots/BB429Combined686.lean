import BB429Combined677
import BB429MoreShifted
import Lean.Elab.Tactic.Omega

/-!
Exact union of the original 673 inverse exclusions, Agent30's first four
shifted exclusions, and nine more source-root exclusions proved using one
common successful 240000-step rank endpoint. The total mask is a necessary
condition for the true blank-root source gateway, not a reachability theorem.
-/
namespace BB429Combined686

def extra9 : List Nat :=
  [6141,19665,49149,65533,81917,98301,114685,163837,229373]

def excluded686 : List Nat := BB429Combined677.excluded677 ++ extra9

theorem excluded686_count : excluded686.length=686 := by
  simp [excluded686, extra9, List.length_append,
    BB429Combined677.excluded677_count]

theorem excluded686_nodup : excluded686.Nodup := by decide

/-- Every genuine source-root halt counter avoids all 686 disjoint
    residue classes modulo 262144, without a time or size cutoff. -/
theorem blank_halt_not_686 (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (hg : b+1=2*a) : a%262144 ∉ excluded686 := by
  intro h
  have hmem : a%262144 ∈ BB429Combined677.excluded677 ++ extra9 := by
    simpa only [excluded686] using h
  obtain hOld | hNew := List.mem_append.mp hmem
  · exact BB429Combined677.blank_halt_not_677 n a b hr hg hOld
  · have hcase : a%262144=6141 ∨ a%262144=19665 ∨
        a%262144=49149 ∨ a%262144=65533 ∨
        a%262144=81917 ∨ a%262144=98301 ∨
        a%262144=114685 ∨ a%262144=163837 ∨
        a%262144=229373 := by simpa [extra9] using hNew
    rcases hcase with h|h|h|h|h|h|h|h|h
    · exact (BB429MoreShifted.blank_halt_not_6141 n a b hr hg) h
    · exact (BB429MoreShifted.blank_halt_not_19665 n a b hr hg) h
    · exact (BB429MoreShifted.blank_halt_not_49149 n a b hr hg) h
    · exact (BB429MoreShifted.blank_halt_not_65533 n a b hr hg) h
    · exact (BB429MoreShifted.blank_halt_not_81917 n a b hr hg) h
    · exact (BB429MoreShifted.blank_halt_not_98301 n a b hr hg) h
    · exact (BB429MoreShifted.blank_halt_not_114685 n a b hr hg) h
    · exact (BB429MoreShifted.blank_halt_not_163837 n a b hr hg) h
    · exact (BB429MoreShifted.blank_halt_not_229373 n a b hr hg) h

/-- Precise necessary survivor mask: 58 original classes at modulus 16384
    intersected with the complement of 686 forbidden modulus-262144
    residues. No surviving residue is asserted reachable from blank. -/
def still242 : List Nat :=
  BB429Combined677.still251.filter (fun r => decide (r ∉ extra9))

theorem still242_count : still242.length=242 := by decide

theorem still242_nodup : still242.Nodup := by decide

theorem still242_iff (u : Nat) :
    u%262144 ∈ still242 ↔
      u%16384 ∈ BB429SurvivorMask.base58 ∧
      u%262144 ∉ excluded686 := by
  constructor
  · intro h
    obtain ⟨hLive,hExtra⟩ := List.mem_filter.mp h
    obtain ⟨hBase,hOld⟩ :=
      (BB429Combined677.still251_iff u).mp hLive
    refine ⟨hBase, ?_⟩
    intro hBad
    have hBad' : u%262144 ∈
        BB429Combined677.excluded677 ++ extra9 := by
      simpa only [excluded686] using hBad
    obtain hOrig | hNew := List.mem_append.mp hBad'
    · exact hOld hOrig
    · exact (of_decide_eq_true hExtra) hNew
  · rintro ⟨hBase,hSafe⟩
    have hOld : u%262144 ∉ BB429Combined677.excluded677 := by
      intro hh
      exact hSafe (List.mem_append.mpr (Or.inl hh))
    have hExtra : u%262144 ∉ extra9 := by
      intro hh
      exact hSafe (List.mem_append.mpr (Or.inr hh))
    apply List.mem_filter.mpr
    constructor
    · exact (BB429Combined677.still251_iff u).mpr ⟨hBase,hOld⟩
    · exact decide_eq_true hExtra

#print axioms excluded686_count
#print axioms excluded686_nodup
#print axioms blank_halt_not_686
#print axioms still242_count
#print axioms still242_nodup
#print axioms still242_iff
end BB429Combined686
