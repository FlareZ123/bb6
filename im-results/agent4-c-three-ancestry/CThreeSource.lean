import CThreeArithmetic
import ThreeConeSource
import GenericSection
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4Three
open BB6.Agent46

/-- Three authentic section edges cannot end at any point in the sector. -/
theorem no_three_edges (u v b l a k s t : Nat)
    (hthird : secNext (u,v)=some (b,l))
    (hsecond : secNext (b,l)=some (a,k))
    (hfirst : secNext (a,k)=some (16*s+9,32*t+36)) : False := by
  have hp1 : sectionPreimageAll a k (16*s+9) (32*t+36) :=
    (section_preimage_all_iff a k (16*s+9) (32*t+36)).mp hfirst
  obtain ⟨ha,hk⟩ := first_parent s t a k hp1
  subst a
  subst k
  have hp2 : sectionPreimageAll b l (16*s+32*t+43) (16*t+17) :=
    (section_preimage_all_iff b l (16*s+32*t+43) (16*t+17)).mp hsecond
  obtain ⟨hb,hl⟩ := second_parent s t b l hp2
  subst b
  subst l
  have hh := BB6.Agent3.section_odd_image u v
    (8*s+24*t+28) (4*s+20*t+21) hthird
    (by omega) (by omega)
  omega

/-- Every successful source run of three or more returns avoids the sector. -/
theorem all_source_no_three (start : Nat×Nat) (n s t : Nat) :
    BB6.Agent8Section.run secNext (n+3) (some start) ≠
      some (16*s+9,32*t+36) := by
  intro ht
  have htime : n+3=((n+1)+1)+1 := by omega
  rw [htime] at ht
  change (BB6.Agent8Section.run secNext ((n+1)+1) (some start)).bind secNext =
    some (16*s+9,32*t+36) at ht
  cases hp : BB6.Agent8Section.run secNext ((n+1)+1) (some start) with
  | none => simp [hp] at ht
  | some p =>
      rcases p with ⟨a,k⟩
      have hfirst : secNext (a,k)=some (16*s+9,32*t+36) := by
        simpa [hp] using ht
      change (BB6.Agent8Section.run secNext (n+1) (some start)).bind secNext =
        some (a,k) at hp
      cases hq : BB6.Agent8Section.run secNext (n+1) (some start) with
      | none => simp [hq] at hp
      | some q =>
          rcases q with ⟨b,l⟩
          have hsecond : secNext (b,l)=some (a,k) := by simpa [hq] using hp
          change (BB6.Agent8Section.run secNext n (some start)).bind secNext =
            some (b,l) at hq
          cases hr : BB6.Agent8Section.run secNext n (some start) with
          | none => simp [hr] at hq
          | some r =>
              rcases r with ⟨u,v⟩
              have hthird : secNext (u,v)=some (b,l) := by
                simpa [hr] using hq
              exact no_three_edges u v b l a k s t hthird hsecond hfirst

/-- The exact blank-root section orbit never enters the sector, at any time. -/
theorem blank_no_sector (time s t : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (16*s+9,32*t+36) := by
  cases time with
  | zero =>
      intro h
      simp [BB6.Agent8Section.run] at h
  | succ n =>
      cases n with
      | zero =>
          intro h
          have he : secNext (5,1)=some (3,4) := by decide
          simp [BB6.Agent8Section.run,he] at h
      | succ n =>
          cases n with
          | zero =>
              intro h
              have he : secNext (5,1)=some (3,4) := by decide
              have hf : secNext (3,4)=some (4,7) := by
                simp [secNext,exactSection,bounce]
              simp [BB6.Agent8Section.run,he,hf] at h
          | succ n =>
              simpa only [show n+1+1+1=n+3 by omega] using
                all_source_no_three (5,1) n s t

#print axioms no_three_edges
#print axioms all_source_no_three
#print axioms blank_no_sector
end BB6.Agent4Three
