import BackwardMod
import CLine

set_option maxHeartbeats 0
namespace A4Backward

theorem nextC_source_equal (a k c : Nat) :
    nextC (a,k,c) = BB6CLine.nextC (a,k,c) := by
  rcases c with _ | _ | _ | _ | d
  · rcases a with _ | _ | a
    · rfl
    · rcases k with _ | k
      · rfl
      · simp [nextC, BB6CLine.nextC]
        omega
    · simp [nextC,BB6CLine.nextC]
  · rfl
  · rfl
  · rfl
  · rcases a with _ | a
    · by_cases he : k%2=0
      · simp [nextC,BB6CLine.nextC,he]
        omega
      · simp [nextC,BB6CLine.nextC,he]
        omega
    · simp [nextC,BB6CLine.nextC]

theorem source_blank_never_bad (s : Nat × Nat × Nat)
    (h : BB6CLine.Reach s) : ¬bad s.1 s.2.1 s.2.2 := by
  induction h with
  | init =>
      simp [bad,low]
  | next x y hx hstep ih =>
      rcases x with ⟨a,k,c⟩
      rcases y with ⟨a',k',c'⟩
      intro hb
      have he : nextC (a,k,c) = some (a',k',c') := by
        rw [nextC_source_equal]
        exact hstep
      exact ih (backward_step a k c a' k' c' he hb)

theorem source_no_cylinder_13_31 (a k : Nat)
    (ha : a%96=13) (hk : k%96=31)
    (h : BB6CLine.Reach (a,k,0)) : False := by
  have hh := source_blank_never_bad (a,k,0) h
  apply hh
  simp [bad,low,ha,hk]

theorem source_no_low_family_18_23 (a k : Nat)
    (ha : a%48=18) (hk : k%24=23)
    (h : BB6CLine.Reach (a,k,0)) : False := by
  have hh := source_blank_never_bad (a,k,0) h
  apply hh
  simp [bad,low,ha,hk]

theorem source_no_low_family_20_0 (a k : Nat)
    (ha : a%48=20) (hk : k%24=0)
    (h : BB6CLine.Reach (a,k,0)) : False := by
  have hh := source_blank_never_bad (a,k,0) h
  apply hh
  simp [bad,low,ha,hk]

theorem source_no_low_family_42_11 (a k : Nat)
    (ha : a%48=42) (hk : k%24=11)
    (h : BB6CLine.Reach (a,k,0)) : False := by
  have hh := source_blank_never_bad (a,k,0) h
  apply hh
  simp [bad,low,ha,hk]

theorem source_no_13_31_0 (h : BB6CLine.Reach (13,31,0)) : False := by
  have hh := source_blank_never_bad (13,31,0) h
  exact hh (by simp [bad,low])

#print axioms nextC_source_equal
#print axioms source_blank_never_bad
#print axioms source_no_cylinder_13_31
#print axioms source_no_low_family_18_23
#print axioms source_no_low_family_20_0
#print axioms source_no_low_family_42_11
#print axioms source_no_13_31_0
end A4Backward
