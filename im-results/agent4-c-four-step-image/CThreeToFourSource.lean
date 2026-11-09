import CThreeArithmetic
import ThreeConeSource
import ThreeConeProper
import GenericSection
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4Four
open BB6.Agent46

/-- A four-return obstruction: the only immediate precursor of
    this target cylinder is in the source-certified strict I₂\I₃ cone. -/
theorem four_edge_impossible (u v c d b l a k x y : Nat)
    (hy : 70 ≤ y) (hs : (x+y)%8=1) (hy32 : y%32=22)
    (h4 : secNext (u,v)=some (c,d))
    (h3 : secNext (c,d)=some (b,l))
    (h2 : secNext (b,l)=some (a,k))
    (h1 : secNext (a,k)=some (x,y)) : False := by
  have hp : sectionPreimageAll a k x y :=
    (section_preimage_all_iff a k x y).mp h1
  obtain ⟨ha,hk⟩ := BB6.Agent4Three.only_direct_mod4_one a k x y
    (by omega) (by omega) (by omega) hp
  have hparent : 34≤k ∧
      (((a+k)%8=1 ∧ k%16=10) ∨ ((a+k)%8=3 ∧ k%16=2)) := by
    constructor
    · omega
    · left
      constructor <;> omega
  exact BB6.Agent34Three.no_three_edges u v c d b l a k
    hparent.1 hparent.2 h4 h3 h2

/-- The four-return obstruction is sharp: every such target really has
    three consecutive source predecessors, while none has four. -/
theorem exactly_three_not_four (x y : Nat)
    (hy : 70≤y) (hs : (x+y)%8=1) (hy32 : y%32=22) :
    (∃ a k b l c d,
      secNext (c,d)=some (b,l) ∧
      secNext (b,l)=some (a,k) ∧
      secNext (a,k)=some (x,y)) ∧
    (∀ u v c d b l a k,
      ¬ (secNext (u,v)=some (c,d) ∧
         secNext (c,d)=some (b,l) ∧
         secNext (b,l)=some (a,k) ∧
         secNext (a,k)=some (x,y))) := by
  let a := x+y-2
  let k := (y-2)/2
  have hfirst : secNext (a,k)=some (x,y) := by
    dsimp [a,k]
    exact BB6.Agent34ThreeProper.direct_predecessor x y (by omega) (by omega)
  have hsector :
      34≤k ∧ (((a+k)%8=1 ∧ k%16=10) ∨
        ((a+k)%8=3 ∧ k%16=2)) := by
    dsimp [a,k]
    constructor
    · omega
    · left
      constructor <;> omega
  obtain ⟨⟨b,l,c,d,hthird,hsecond⟩,_⟩ :=
    BB6.Agent34ThreeProper.exactly_two_not_three a k hsector.1 hsector.2
  constructor
  · exact ⟨a,k,b,l,c,d,hthird,hsecond,hfirst⟩
  · intro u v c d b l a' k' ⟨h4,h3,h2,h1⟩
    exact four_edge_impossible u v c d b l a' k' x y hy hs hy32
      h4 h3 h2 h1

/-- Every real blank-origin section return avoids this cylinder. -/
theorem blank_no_four_cylinder (time x y : Nat)
    (hy : 70 ≤ y) (hs : (x+y)%8=1) (hy32 : y%32=22) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (x,y) := by
  cases time with
  | zero =>
      intro ht
      simp [BB6.Agent8Section.run] at ht
      omega
  | succ n =>
      intro ht
      change (BB6.Agent8Section.run secNext n (some (5,1))).bind secNext =
        some (x,y) at ht
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none => simp [hp] at ht
      | some p =>
          rcases p with ⟨a,k⟩
          have hfirst : secNext (a,k)=some (x,y) := by
            simpa [hp] using ht
          have hpre : sectionPreimageAll a k x y :=
            (section_preimage_all_iff a k x y).mp hfirst
          obtain ⟨ha,hk⟩ := BB6.Agent4Three.only_direct_mod4_one a k x y
            (by omega) (by omega) (by omega) hpre
          have hsector :
              34≤k ∧ (((a+k)%8=1 ∧ k%16=10) ∨
                ((a+k)%8=3 ∧ k%16=2)) := by
            constructor
            · omega
            · left
              constructor <;> omega
          exact BB6.Agent34Three.cone_blank_unreachable n a k
            hsector.1 hsector.2 hp

private theorem power_margin (r : Nat) :
    3*(r+3)+25 ≤ (2:Nat)^(2*(r+3)+2) := by
  induction r with
  | zero => decide
  | succ r ih =>
      have he : 2*(r+1+3)+2=(2*(r+3)+2)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

/-- An infinite high-stopping parameter lattice is excluded from the
    true original Machine C blank section, without a time cutoff. -/
theorem high_stop_fourth_exclusion (j m k time : Nat)
    (hm : 3≤m) (hj : j%4=0) (hm4 : m%4=3)
    (hpair : (j+3*m+5)%32=10)
    (hstop : k+j+3*m+5=(2:Nat)^(2*m+2)*(j+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*j+3,k) := by
  have hpow32 : 32 ∣ (2:Nat)^(2*m+2) := by
    have hd : (2:Nat)^5 ∣ (2:Nat)^(2*m+2) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa using hd
  rcases hpow32 with ⟨q,hq⟩
  have hmod : (k+j+3*m+5)%32=0 := by
    apply Nat.mod_eq_zero_of_dvd
    refine ⟨q*(j+3),?_⟩
    calc
      k+j+3*m+5=(2:Nat)^(2*m+2)*(j+3) := hstop
      _=(32*q)*(j+3) := by rw [hq]
      _=32*(q*(j+3)) := by ac_rfl
  have hkmod : k%32=22 := by omega
  have hsum : (2*j+3+k)%8=1 := by omega
  have hrep : m=(m-3)+3 := by omega
  have hpow := power_margin (m-3)
  rw [←hrep] at hpow
  have hp : 1≤(2:Nat)^(2*m+2) := Nat.pow_pos (by decide)
  have hjbound : j≤(2:Nat)^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  have hmargin : 3*(3*m+25) ≤ 3*(2:Nat)^(2*m+2) :=
    Nat.mul_le_mul_left 3 hpow
  have hmul : (2:Nat)^(2*m+2)*(j+3)=
      (2:Nat)^(2*m+2)*j+3*(2:Nat)^(2*m+2) := by
    rw [Nat.mul_add]
    ac_rfl
  have hbound : 70≤k := by
    rw [hmul] at hstop
    omega
  exact blank_no_four_cylinder time (2*j+3) k hbound hsum hkmod

#print axioms four_edge_impossible
#print axioms exactly_three_not_four
#print axioms blank_no_four_cylinder
#print axioms high_stop_fourth_exclusion
end BB6.Agent4Four
