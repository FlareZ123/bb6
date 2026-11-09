import ThreeConeArithmetic
import SectionAllInverse
import Agent3CImage
import GenericSection
import Lean.Elab.Tactic.Omega

namespace BB6.Agent34Three
open BB6.Agent46

/-- Transfer true original section edges to the exact predecessor grammar. -/
theorem source_two_forced (a k b l x y : Nat)
    (hy : 34≤y)
    (hsector : ((x+y)%8=1 ∧ y%16=10) ∨
               ((x+y)%8=3 ∧ y%16=2))
    (hfirst : secNext (a,k)=some (x,y))
    (hsecond : secNext (b,l)=some (a,k)) :
    5≤l ∧ l%2=1 ∧ (b+l)%4=2 := by
  have hcopy1 : sectionPreimageAll a k x y :=
    (BB6.Agent46.section_preimage_all_iff a k x y).mp hfirst
  have hcopy2 : sectionPreimageAll b l a k :=
    (BB6.Agent46.section_preimage_all_iff b l a k).mp hsecond
  exact two_forced a k b l x y hy hsector hcopy1 hcopy2

/-- No three consecutive original first-return section edges end here. -/
theorem no_three_edges (u v b l a k x y : Nat)
    (hy : 34≤y)
    (hsector : ((x+y)%8=1 ∧ y%16=10) ∨
               ((x+y)%8=3 ∧ y%16=2))
    (hthird : secNext (u,v)=some (b,l))
    (hsecond : secNext (b,l)=some (a,k))
    (hfirst : secNext (a,k)=some (x,y)) : False := by
  obtain ⟨hbound,hodd,hmod⟩ :=
    source_two_forced a k b l x y hy hsector hfirst hsecond
  have hh := BB6.Agent3.section_odd_image u v b l hthird hbound hodd
  omega

/-- After three or more section returns, the residue cone is forbidden
from every possible original source state. -/
theorem all_source_no_three (start : Nat×Nat) (n x y : Nat)
    (hy : 34≤y)
    (hsector : ((x+y)%8=1 ∧ y%16=10) ∨
               ((x+y)%8=3 ∧ y%16=2)) :
    BB6.Agent8Section.run secNext (n+3) (some start) ≠ some (x,y) := by
  intro ht
  have htime : n+3=((n+1)+1)+1 := by omega
  rw [htime] at ht
  change (BB6.Agent8Section.run secNext ((n+1)+1) (some start)).bind secNext =
    some (x,y) at ht
  cases hp : BB6.Agent8Section.run secNext ((n+1)+1) (some start) with
  | none => simp [hp] at ht
  | some p =>
      rcases p with ⟨a,k⟩
      have hfirst : secNext (a,k)=some (x,y) := by simpa [hp] using ht
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
              have hthird : secNext (u,v)=some (b,l) := by simpa [hr] using hq
              exact no_three_edges u v b l a k x y hy hsector hthird hsecond hfirst

/-- Genuine blank-origin exclusion, including initial times zero,
one, two, when the right coordinates are respectively 1,4,7. -/
theorem cone_blank_unreachable (time x y : Nat)
    (hy : 34≤y)
    (hsector : ((x+y)%8=1 ∧ y%16=10) ∨
               ((x+y)%8=3 ∧ y%16=2)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (x,y) := by
  cases time with
  | zero =>
      intro h
      simp [BB6.Agent8Section.run] at h
      omega
  | succ n =>
      cases n with
      | zero =>
          intro h
          have he : secNext (5,1)=some (3,4) := by decide
          simp [BB6.Agent8Section.run,he] at h
          omega
      | succ n =>
          cases n with
          | zero =>
              intro h
              have he : secNext (5,1)=some (3,4) := by decide
              have hf : secNext (3,4)=some (4,7) := by
                simp [secNext, exactSection, bounce]
              simp [BB6.Agent8Section.run,he,hf] at h
              omega
          | succ n =>
              simpa only [show n+1+1+1=n+3 by omega] using
                all_source_no_three (5,1) n x y hy hsector

/-- Pullback of the raw residue cone through the exact high-halting
stopping equation for eight congruence classes modulo 16. -/
theorem high_stop_sector (j m k : Nat)
    (hparams :
      (j%16=2 ∧ m%16=5) ∨
      (j%16=6 ∧ m%16=9) ∨
      (j%16=10 ∧ m%16=13) ∨
      (j%16=14 ∧ m%16=1) ∨
      (j%16=3 ∧ m%16=2) ∨
      (j%16=7 ∧ m%16=6) ∨
      (j%16=11 ∧ m%16=10) ∨
      (j%16=15 ∧ m%16=14))
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ((2*j+3+k)%8=1 ∧ k%16=10) ∨
    ((2*j+3+k)%8=3 ∧ k%16=2) := by
  have hm : 1≤m := by omega
  have hp16 : 16 ∣ (2:Nat)^(2*m+2) := by
    change (2:Nat)^4 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨u,hu⟩ := hp16
  have hmul : 16∣k+j+3*m+5 := by
    refine ⟨u*(j+3),?_⟩
    calc
      k+j+3*m+5 = 2^(2*m+2)*(j+3) := hgate
      _=(16*u)*(j+3) := by rw [hu]
      _=16*(u*(j+3)) := by ac_rfl
  have hmod : (k+j+3*m+5)%16=0 := Nat.mod_eq_zero_of_dvd hmul
  omega

/-- Eight infinite parameter families excluded from the genuine
blank-origin section orbit whenever the stopping right counter >=34. -/
theorem high_stop_blank_unreachable (j m k time : Nat)
    (hy : 34≤k)
    (hparams :
      (j%16=2 ∧ m%16=5) ∨
      (j%16=6 ∧ m%16=9) ∨
      (j%16=10 ∧ m%16=13) ∨
      (j%16=14 ∧ m%16=1) ∨
      (j%16=3 ∧ m%16=2) ∨
      (j%16=7 ∧ m%16=6) ∨
      (j%16=11 ∧ m%16=10) ∨
      (j%16=15 ∧ m%16=14))
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*j+3,k) := by
  have hres := high_stop_sector j m k hparams hgate
  exact cone_blank_unreachable time (2*j+3) k hy hres

#print axioms source_two_forced
#print axioms no_three_edges
#print axioms all_source_no_three
#print axioms cone_blank_unreachable
#print axioms high_stop_blank_unreachable
end BB6.Agent34Three
