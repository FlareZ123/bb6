import FullForcedFilter
import Lean.Elab.Tactic.Omega

namespace BB6.Agent12ForcedLattice
open BB6.Agent3 BB6.Agent46

/-- For the exact inverse itinerary, (P,A) gives the final right shift
    (v + A*(u+2*v))/P, in units of sixteen cells. -/
def signature (x y : Nat) : Nat × Nat :=
  if h : oddLowGate x y then
    let s := signature ((x+y-4)/2) ((x+3*y-10)/4)
    (4*s.1,4*s.2+1)
  else if he : evenSevenGate x y then
    let s := signature ((x+y-5)/2) ((x+3*y-9)/4)
    (4*s.1,4*s.2+1)
  else if hf : evenAffineGate x y then
    let s := signature (x+y-2) ((y-2)/2)
    (2*s.1,2*s.2)
  else if hs : sixEvenRightGate x y then
    let s := signature (x+y-2) ((y-2)/2)
    (2*s.1,2*s.2)
  else (1,0)
termination_by x+2*y
decreasing_by
  all_goals
    simp_wf
    simp only [oddLowGate,evenSevenGate,evenAffineGate,sixEvenRightGate] at *
    omega

def admissible (x y u v : Nat) : Prop :=
  let s := signature x y
  s.1 ∣ v+s.2*(u+2*v)

private theorem quad_arith (p a u v : Nat)
    (h : 4*p ∣ v+(4*a+1)*(u+2*v)) :
    (u+3*v)%4=0 ∧ (u+v)%2=0 ∧
    p ∣ (u+3*v)/4+a*((u+v)/2+2*((u+3*v)/4)) := by
  obtain ⟨k,hk⟩ := h
  simp only [Nat.add_mul,Nat.one_mul,Nat.mul_assoc] at hk
  have h4 : (u+3*v)%4=0 := by omega
  have h2 : (u+v)%2=0 := by omega
  have hw : (u+v)/2+2*((u+3*v)/4)=u+2*v := by omega
  refine ⟨h4,h2,k,?_⟩
  rw [hw]
  omega

private theorem half_arith (p a u v : Nat)
    (h : 2*p ∣ v+(2*a)*(u+2*v)) :
    v%2=0 ∧ p ∣ v/2+a*(u+v+2*(v/2)) := by
  obtain ⟨k,hk⟩ := h
  simp only [Nat.mul_assoc] at hk
  have h2 : v%2=0 := by omega
  have hw : u+v+2*(v/2)=u+2*v := by omega
  refine ⟨h2,k,?_⟩
  rw [hw]
  omega

private theorem quad_shift (x y u v c e : Nat)
    (hx : c≤x+y) (hy : e≤x+3*y)
    (h4 : (u+3*v)%4=0) (h2 : (u+v)%2=0) :
    (x+16*u+(y+16*v)-c)/2 = (x+y-c)/2+16*((u+v)/2) ∧
    (x+16*u+3*(y+16*v)-e)/4 = (x+3*y-e)/4+16*((u+3*v)/4) := by
  omega

private theorem half_shift (x y u v : Nat) (hy : 2≤y) (h2 : v%2=0) :
    x+16*u+(y+16*v)-2 = x+y-2+16*(u+v) ∧
    (y+16*v-2)/2 = (y-2)/2+16*(v/2) := by omega

private theorem odd_norm {x y : Nat} (h : oddLowGate x y) :
    fullForcedNormalize x y = fullForcedNormalize ((x+y-4)/2) ((x+3*y-10)/4) := by
  conv => lhs; unfold fullForcedNormalize
  rw [dite_eq_left h]
private theorem seven_norm {x y : Nat} (h : evenSevenGate x y) :
    fullForcedNormalize x y = fullForcedNormalize ((x+y-5)/2) ((x+3*y-9)/4) := by
  have hO : ¬ oddLowGate x y := by unfold oddLowGate evenSevenGate at *; omega
  conv => lhs; unfold fullForcedNormalize
  rw [dite_eq_right hO, dite_eq_left h]
private theorem affine_norm {x y : Nat} (h : evenAffineGate x y) :
    fullForcedNormalize x y = fullForcedNormalize (x+y-2) ((y-2)/2) := by
  have hO : ¬ oddLowGate x y := by unfold oddLowGate evenAffineGate at *; omega
  have hS : ¬ evenSevenGate x y := by unfold evenSevenGate evenAffineGate at *; omega
  conv => lhs; unfold fullForcedNormalize
  rw [dite_eq_right hO, dite_eq_right hS, dite_eq_left h]
private theorem six_norm {x y : Nat} (h : sixEvenRightGate x y) :
    fullForcedNormalize x y = fullForcedNormalize (x+y-2) ((y-2)/2) := by
  have hO : ¬ oddLowGate x y := by unfold oddLowGate sixEvenRightGate at *; omega
  have hS : ¬ evenSevenGate x y := by unfold evenSevenGate sixEvenRightGate at *; omega
  by_cases hA : evenAffineGate x y
  · exact affine_norm hA
  · conv => lhs; unfold fullForcedNormalize
    rw [dite_eq_right hO, dite_eq_right hS, dite_eq_right hA, dite_eq_left h]

private theorem excluded_congr {x y x' y' : Nat}
    (h : fullForcedNormalize x y = fullForcedNormalize x' y') :
    fullForcedExcluded x y = fullForcedExcluded x' y' := by
  unfold fullForcedExcluded
  rw [h]

private def bad (x y : Nat) : Prop :=
  5≤y ∧ y%2=1 ∧ ((x+y)%4=1 ∨ (x+y)%4=2)
private theorem bad_terminal {x y : Nat} (h : bad x y) :
    fullForcedNormalize x y = (x,y) := by
  have hO : ¬ oddLowGate x y := by unfold oddLowGate bad at *; omega
  have hS : ¬ evenSevenGate x y := by unfold evenSevenGate bad at *; omega
  have hA : ¬ evenAffineGate x y := by unfold evenAffineGate bad at *; omega
  have hE : ¬ sixEvenRightGate x y := by unfold sixEvenRightGate bad at *; omega
  conv => lhs; unfold fullForcedNormalize
  rw [dite_eq_right hO, dite_eq_right hS, dite_eq_right hA, dite_eq_right hE]
private theorem excluded_of_bad {x y : Nat} (h : bad x y) :
    fullForcedExcluded x y = true := by
  unfold fullForcedExcluded
  rw [bad_terminal h]
  exact decide_eq_true h

/-- A coupled congruence, rather than two independent modulus conditions,
    is sufficient to preserve the entire rejecting inverse itinerary. -/
theorem fullForcedExcluded_lattice (x y u v : Nat)
    (h : fullForcedExcluded x y=true) (ha : admissible x y u v) :
    fullForcedExcluded (x+16*u) (y+16*v)=true := by
  generalize hz : x+2*y=z
  induction z using Nat.strongRecOn generalizing x y u v with
  | ind z ih =>
    by_cases hO : oddLowGate x y
    · let X := (x+y-4)/2
      let Y := (x+3*y-10)/4
      have hsig : signature x y=(4*(signature X Y).1,4*(signature X Y).2+1) := by
        conv => lhs; unfold signature
        rw [dite_eq_left hO]
      unfold admissible at ha
      rw [hsig] at ha
      obtain ⟨h4,h2,had⟩ := quad_arith _ _ u v ha
      have hchild : fullForcedExcluded X Y=true := by
        rw [excluded_congr (odd_norm hO)] at h
        exact h
      have hlt : X+2*Y<z := by dsimp [X,Y]; unfold oddLowGate at hO; omega
      have hx : 4≤x+y := by unfold oddLowGate at hO; omega
      have hy : 10≤x+3*y := by unfold oddLowGate at hO; omega
      have hg : oddLowGate (x+16*u) (y+16*v) := by unfold oddLowGate at *; omega
      obtain ⟨hxs,hys⟩ := quad_shift x y u v 4 10 hx hy h4 h2
      rw [excluded_congr (odd_norm hg),hxs,hys]
      exact ih _ hlt X Y _ _ hchild had rfl
    · by_cases hS : evenSevenGate x y
      · let X := (x+y-5)/2
        let Y := (x+3*y-9)/4
        have hsig : signature x y=(4*(signature X Y).1,4*(signature X Y).2+1) := by
          conv => lhs; unfold signature
          rw [dite_eq_right hO,dite_eq_left hS]
        unfold admissible at ha
        rw [hsig] at ha
        obtain ⟨h4,h2,had⟩ := quad_arith _ _ u v ha
        have hchild : fullForcedExcluded X Y=true := by
          rw [excluded_congr (seven_norm hS)] at h
          exact h
        have hlt : X+2*Y<z := by dsimp [X,Y]; unfold evenSevenGate at hS; omega
        have hx : 5≤x+y := by unfold evenSevenGate at hS; omega
        have hy : 9≤x+3*y := by unfold evenSevenGate at hS; omega
        have hg : evenSevenGate (x+16*u) (y+16*v) := by unfold evenSevenGate at *; omega
        obtain ⟨hxs,hys⟩ := quad_shift x y u v 5 9 hx hy h4 h2
        rw [excluded_congr (seven_norm hg),hxs,hys]
        exact ih _ hlt X Y _ _ hchild had rfl
      · by_cases hA : evenAffineGate x y
        · let X := x+y-2
          let Y := (y-2)/2
          have hsig : signature x y=(2*(signature X Y).1,2*(signature X Y).2) := by
            conv => lhs; unfold signature
            rw [dite_eq_right hO,dite_eq_right hS,dite_eq_left hA]
          unfold admissible at ha
          rw [hsig] at ha
          obtain ⟨h2,had⟩ := half_arith _ _ u v ha
          have hchild : fullForcedExcluded X Y=true := by
            rw [excluded_congr (affine_norm hA)] at h
            exact h
          have hlt : X+2*Y<z := by dsimp [X,Y]; unfold evenAffineGate at hA; omega
          have hy : 2≤y := by unfold evenAffineGate at hA; omega
          have hg : evenAffineGate (x+16*u) (y+16*v) := by unfold evenAffineGate at *; omega
          obtain ⟨hxs,hys⟩ := half_shift x y u v hy h2
          rw [excluded_congr (affine_norm hg),hxs,hys]
          exact ih _ hlt X Y _ _ hchild had rfl
        · by_cases hE : sixEvenRightGate x y
          · let X := x+y-2
            let Y := (y-2)/2
            have hsig : signature x y=(2*(signature X Y).1,2*(signature X Y).2) := by
              conv => lhs; unfold signature
              rw [dite_eq_right hO,dite_eq_right hS,dite_eq_right hA,dite_eq_left hE]
            unfold admissible at ha
            rw [hsig] at ha
            obtain ⟨h2,had⟩ := half_arith _ _ u v ha
            have hchild : fullForcedExcluded X Y=true := by
              rw [excluded_congr (six_norm hE)] at h
              exact h
            have hlt : X+2*Y<z := by dsimp [X,Y]; unfold sixEvenRightGate at hE; omega
            have hy : 2≤y := by unfold sixEvenRightGate at hE; omega
            have hg : sixEvenRightGate (x+16*u) (y+16*v) := by unfold sixEvenRightGate at *; omega
            obtain ⟨hxs,hys⟩ := half_shift x y u v hy h2
            rw [excluded_congr (six_norm hg),hxs,hys]
            exact ih _ hlt X Y _ _ hchild had rfl
          · have hn : fullForcedNormalize x y=(x,y) := by
              conv => lhs; unfold fullForcedNormalize
              rw [dite_eq_right hO,dite_eq_right hS,dite_eq_right hA,dite_eq_right hE]
            unfold fullForcedExcluded at h
            rw [hn] at h
            have hb : bad x y := by unfold bad; exact of_decide_eq_true h
            apply excluded_of_bad
            unfold bad at *
            omega

theorem blank_unreachable_lattice (x y u v : Nat)
    (h : fullForcedExcluded x y=true) (ha : admissible x y u v) (time : Nat) :
    BB6.Agent8Section.run BB6.Agent46.secNext time (some (5,1)) ≠
      some (x+16*u,y+16*v) :=
  fullForcedExcluded_sound _ _ (fullForcedExcluded_lattice x y u v h ha) time

#print axioms fullForcedExcluded_lattice
#print axioms blank_unreachable_lattice
end BB6.Agent12ForcedLattice
