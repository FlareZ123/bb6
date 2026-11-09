import CThreeArithmetic
import ThreeConeSource
import GenericSection
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4Three
open BB6.Agent46

/-- The parity-diagonal strip has no three-edge authentic section ancestry. -/
theorem no_three_edges_alt (u v b l a k s t : Nat)
    (hparity : s%2=t%2)
    (hthird : secNext (u,v)=some (b,l))
    (hsecond : secNext (b,l)=some (a,k))
    (hfirst : secNext (a,k)=some (8*s+5,16*t+12)) : False := by
  have hp1 : sectionPreimageAll a k (8*s+5) (16*t+12) :=
    (section_preimage_all_iff a k (8*s+5) (16*t+12)).mp hfirst
  obtain ⟨ha,hk⟩ := first_parent_alt s t a k hp1
  subst a
  subst k
  have hp2 : sectionPreimageAll b l (8*s+56*t+15) (8*t+5) :=
    (section_preimage_all_iff b l (8*s+56*t+15) (8*t+5)).mp hsecond
  obtain ⟨hb,hl⟩ := second_parent_alt s t b l hp2
  subst b
  subst l
  have hh := BB6.Agent3.section_odd_image u v
    (4*s+12*t+8) (2*s+10*t+5) hthird
    (by omega) (by omega)
  omega

/-- From any source there are no three consecutive edges ending in the strip. -/
theorem all_source_no_three_alt (start : Nat×Nat) (n s t : Nat)
    (hparity : s%2=t%2) :
    BB6.Agent8Section.run secNext (n+3) (some start) ≠
      some (8*s+5,16*t+12) := by
  intro ht
  have htime : n+3=((n+1)+1)+1 := by omega
  rw [htime] at ht
  change (BB6.Agent8Section.run secNext ((n+1)+1) (some start)).bind secNext =
    some (8*s+5,16*t+12) at ht
  cases hp : BB6.Agent8Section.run secNext ((n+1)+1) (some start) with
  | none => simp [hp] at ht
  | some p =>
      rcases p with ⟨a,k⟩
      have hfirst : secNext (a,k)=some (8*s+5,16*t+12) := by
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
              exact no_three_edges_alt u v b l a k s t hparity
                hthird hsecond hfirst

/-- The authentic blank section never reaches the parity-diagonal strip. -/
theorem blank_no_strip_alt (time s t : Nat) (hparity : s%2=t%2) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (8*s+5,16*t+12) := by
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
                all_source_no_three_alt (5,1) n s t hparity

/-- Additional sharp sector with x=5 mod16 and y=12 mod32. -/
theorem blank_no_sector_c (time s t : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (16*s+5,32*t+12) := by
  simpa only [show 8*(2*s)+5=16*s+5 by omega,
    show 16*(2*t)+12=32*t+12 by omega] using
    (blank_no_strip_alt time (2*s) (2*t) (by omega))

/-- Additional sharp sector with x=13 mod16 and y=28 mod32. -/
theorem blank_no_sector_d (time s t : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (16*s+13,32*t+28) := by
  simpa only [show 8*(2*s+1)+5=16*s+13 by omega,
    show 16*(2*t+1)+12=32*t+28 by omega] using
    (blank_no_strip_alt time (2*s+1) (2*t+1) (by omega))

#print axioms no_three_edges_alt
#print axioms all_source_no_three_alt
#print axioms blank_no_strip_alt
#print axioms blank_no_sector_c
#print axioms blank_no_sector_d
end BB6.Agent4Three
