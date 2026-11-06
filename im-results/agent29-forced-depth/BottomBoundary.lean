import SectionAllInverse
import Agent38SectionParity
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29Bottom
open BB6.Agent46

/-- Source-complete inverse grammar: a section return with right counter
    one can only be the special edge (1,0) -> (5,1). -/
theorem right_one_only_special (a k x : Nat)
    (h : secNext (a,k)=some (x,1)) :
    a=1 ∧ k=0 ∧ x=5 := by
  have hp := (section_preimage_all_iff a k x 1).mp h
  unfold sectionPreimageAll at hp
  by_cases ha0 : a=0
  · simp [ha0] at hp
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [ha0,ha1,hk0] at hp
        omega
      · simp [ha0,ha1,hk0] at hp
    · by_cases hk0 : k=0
      · simp [ha0,ha1,hk0] at hp
      · by_cases hlow : 2*k≤a
        · simp [ha0,ha1,hk0,hlow] at hp
        · by_cases heven : a%2=0
          · simp [ha0,ha1,hk0,hlow,heven] at hp
          · simp [ha0,ha1,hk0,hlow,heven] at hp
/-- The blank-start section visits right counter one only at time zero. -/
theorem no_post_blank_right_one (n x : Nat) :
    BB6.Agent8Section.run secNext (n+1) (some (5,1)) ≠ some (x,1) := by
  intro h
  cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
  | none => simp [BB6.Agent8Section.run,hp] at h
  | some p =>
      obtain ⟨a,k⟩ := p
      have he : secNext (a,k)=some (x,1) := by
        simpa [BB6.Agent8Section.run,hp] using h
      obtain ⟨_,hk,_⟩ := right_one_only_special a k x he
      have hpos := BB6Agent38.blank_section_positive n a k hp
      omega

private theorem even_bounce_sum (n a : Nat) :
    (2^n*(2*(a-1)+6))%2=0 := by
  have heq : 2*(a-1)+6=2*((a-1)+3) := by omega
  rw [heq]
  have hf : 2^n*(2*((a-1)+3))=2*(2^n*((a-1)+3)) := by ac_rfl
  rw [hf]
  omega

/-- An odd first coordinate together with right counter four
    has exactly one possible section predecessor, the direct
    parent with right counter one. -/
theorem odd_four_only_direct_parent (a k x : Nat)
    (hx : x%2=1)
    (h : secNext (a,k)=some (x,4)) :
    a=x+2 ∧ k=1 := by
  have hp := (section_preimage_all_iff a k x 4).mp h
  unfold sectionPreimageAll at hp
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [ha0,hk0] at hp
    · by_cases hk1 : k=1
      · simp [ha0,hk0,hk1] at hp
        omega
      · simp [ha0,hk0,hk1] at hp
        obtain ⟨n,hs,_⟩ := hp
        have hev : (2^n*8)%2=0 := by omega
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [ha0,ha1,hk0] at hp
      · by_cases hk1 : k=1
        · simp [ha0,ha1,hk0,hk1] at hp
        · by_cases hk2 : k=2
          · simp [ha0,ha1,hk0,hk1,hk2] at hp
          · by_cases hk3 : k=3
            · simp [ha0,ha1,hk0,hk1,hk2,hk3] at hp
            · simp [ha0,ha1,hk0,hk1,hk2,hk3] at hp
    · by_cases hk0 : k=0
      · simp [ha0,ha1,hk0] at hp
      · by_cases hlow : 2*k≤a
        · simp [ha0,ha1,hk0,hlow] at hp
          omega
        · by_cases heven : a%2=0
          · simp [ha0,ha1,hk0,hlow,heven] at hp
            obtain ⟨n,hs,_⟩ := hp
            have hev : (2^n*(2*(a-1)+6))%2=0 := even_bounce_sum n a
            omega
          · simp [ha0,ha1,hk0,hlow,heven] at hp
/-- The sole odd-first/right-four state on the entire genuine
    blank section orbit is (3,4), and it occurs exactly at time one. -/
theorem blank_odd_four_exact_time (n x : Nat)
    (hx : x%2=1)
    (h : BB6.Agent8Section.run secNext n (some (5,1))=some (x,4)) :
    n=1 ∧ x=3 := by
  cases n with
  | zero => simp [BB6.Agent8Section.run] at h
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at h
      | some p =>
          obtain ⟨a,k⟩ := p
          have he : secNext (a,k)=some (x,4) := by
            simpa [BB6.Agent8Section.run,hp] using h
          obtain ⟨ha,hk⟩ := odd_four_only_direct_parent a k x hx he
          cases n with
          | zero =>
              have hb : (5,1)=(a,k) := by
                simpa [BB6.Agent8Section.run] using hp
              have h5 := congrArg Prod.fst hb
              dsimp at h5
              exact ⟨rfl,by omega⟩
          | succ n =>
              have hparent :
                BB6.Agent8Section.run secNext (n+1) (some (5,1))=
                   some (a,1) := by simpa [hk] using hp
              exact False.elim (no_post_blank_right_one n a hparent)

theorem blank_odd_four_gt_three_unreachable (time x : Nat)
    (hx : x%2=1) (hlarge : 3<x) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (x,4) := by
  intro h
  have hi := blank_odd_four_exact_time time x hx h
  omega

#print axioms right_one_only_special
#print axioms no_post_blank_right_one
#print axioms odd_four_only_direct_parent
#print axioms blank_odd_four_exact_time
#print axioms blank_odd_four_gt_three_unreachable
end BB6.Agent29Bottom
