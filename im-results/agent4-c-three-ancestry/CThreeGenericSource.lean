import CThreeArithmetic
import ThreeConeSource
import GenericSection
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4Three
open BB6.Agent46

/-- The parity-diagonal strip has no three-edge authentic section ancestry. -/
theorem no_three_edges_generic (u v b l a k s t : Nat)
    (hparity : s%2=t%2)
    (hthird : secNext (u,v)=some (b,l))
    (hsecond : secNext (b,l)=some (a,k))
    (hfirst : secNext (a,k)=some (8*s+1,16*t+20)) : False := by
  have hp1 : sectionPreimageAll a k (8*s+1) (16*t+20) :=
    (section_preimage_all_iff a k (8*s+1) (16*t+20)).mp hfirst
  obtain ⟨ha,hk⟩ := first_parent_generic s t a k hp1
  subst a
  subst k
  have hp2 : sectionPreimageAll b l (8*s+16*t+19) (8*t+9) :=
    (section_preimage_all_iff b l (8*s+16*t+19) (8*t+9)).mp hsecond
  obtain ⟨hb,hl⟩ := second_parent_generic s t b l hp2
  subst b
  subst l
  have hh := BB6.Agent3.section_odd_image u v
    (4*s+12*t+12) (2*s+10*t+9) hthird
    (by omega) (by omega)
  omega

/-- From any source there are no three consecutive edges ending in the strip. -/
theorem all_source_no_three_generic (start : Nat×Nat) (n s t : Nat)
    (hparity : s%2=t%2) :
    BB6.Agent8Section.run secNext (n+3) (some start) ≠
      some (8*s+1,16*t+20) := by
  intro ht
  have htime : n+3=((n+1)+1)+1 := by omega
  rw [htime] at ht
  change (BB6.Agent8Section.run secNext ((n+1)+1) (some start)).bind secNext =
    some (8*s+1,16*t+20) at ht
  cases hp : BB6.Agent8Section.run secNext ((n+1)+1) (some start) with
  | none => simp [hp] at ht
  | some p =>
      rcases p with ⟨a,k⟩
      have hfirst : secNext (a,k)=some (8*s+1,16*t+20) := by
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
              exact no_three_edges_generic u v b l a k s t hparity
                hthird hsecond hfirst

/-- The authentic blank section never reaches the parity-diagonal strip. -/
theorem blank_no_strip (time s t : Nat) (hparity : s%2=t%2) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (8*s+1,16*t+20) := by
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
                all_source_no_three_generic (5,1) n s t hparity

/-- Second disjoint blank-unreachable cylinder, at x=1 mod16 and y=20 mod32. -/
theorem blank_no_sector_b (time s t : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (16*s+1,32*t+20) := by
  simpa only [show 8*(2*s)+1=16*s+1 by omega,
    show 16*(2*t)+20=32*t+20 by omega] using
    (blank_no_strip time (2*s) (2*t) (by omega))

#print axioms no_three_edges_generic
#print axioms all_source_no_three_generic
#print axioms blank_no_strip
#print axioms blank_no_sector_b
end BB6.Agent4Three
