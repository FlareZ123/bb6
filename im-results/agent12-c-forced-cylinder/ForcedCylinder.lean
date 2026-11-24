import FullForcedFilter
import Lean.Elab.Tactic.Omega

namespace BB6.Agent12ForcedCylinder
open BB6.Agent3 BB6.Agent46

/-- Bit precision consumed by the exact four-sector inverse itinerary. -/
def precision (x y : Nat) : Nat :=
  if h : oddLowGate x y then
    precision ((x+y-4)/2) ((x+3*y-10)/4) + 2
  else if he : evenSevenGate x y then
    precision ((x+y-5)/2) ((x+3*y-9)/4) + 2
  else if hf : evenAffineGate x y then
    precision (x+y-2) ((y-2)/2) + 1
  else if hs : sixEvenRightGate x y then
    precision (x+y-2) ((y-2)/2) + 1
  else 0
termination_by x+2*y
decreasing_by
  all_goals
    simp_wf
    simp only [oddLowGate,evenSevenGate,evenAffineGate,sixEvenRightGate] at *
    omega

def scale (d : Nat) : Nat := 16*2^d

def bad (x y : Nat) : Prop :=
  5≤y ∧ y%2=1 ∧ ((x+y)%4=1 ∨ (x+y)%4=2)

private theorem scale_one (d : Nat) : scale (d+1)=2*scale d := by
  simp only [scale, Nat.pow_add, Nat.reducePow]
  omega
private theorem scale_two (d : Nat) : scale (d+2)=4*scale d := by
  simp only [scale, Nat.pow_add, Nat.reducePow]
  omega

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

private theorem bad_terminal {x y : Nat} (h : bad x y) :
    fullForcedNormalize x y = (x,y) := by
  have hO : ¬ oddLowGate x y := by unfold oddLowGate bad at *; omega
  have hS : ¬ evenSevenGate x y := by unfold evenSevenGate bad at *; omega
  have hA : ¬ evenAffineGate x y := by unfold evenAffineGate bad at *; omega
  have hE : ¬ sixEvenRightGate x y := by unfold sixEvenRightGate bad at *; omega
  conv => lhs; unfold fullForcedNormalize
  rw [dite_eq_right hO, dite_eq_right hS, dite_eq_right hA, dite_eq_right hE]

private theorem excluded_of_bad {x y : Nat} (h : bad x y) : fullForcedExcluded x y = true := by
  unfold fullForcedExcluded
  rw [bad_terminal h]
  exact decide_eq_true h

private theorem excluded_congr {x y x' y' : Nat}
    (h : fullForcedNormalize x y = fullForcedNormalize x' y') :
    fullForcedExcluded x y = fullForcedExcluded x' y' := by
  unfold fullForcedExcluded
  rw [h]

private theorem odd_gate_lift {x y : Nat} (h : oddLowGate x y) (d u v : Nat) :
    oddLowGate (x+scale d*u) (y+scale d*v) := by
  unfold oddLowGate at *
  simp only [scale,Nat.mul_assoc]
  omega
private theorem seven_gate_lift {x y : Nat} (h : evenSevenGate x y) (d u v : Nat) :
    evenSevenGate (x+scale d*u) (y+scale d*v) := by
  unfold evenSevenGate at *
  simp only [scale,Nat.mul_assoc]
  omega
private theorem affine_gate_lift {x y : Nat} (h : evenAffineGate x y) (d u v : Nat) :
    evenAffineGate (x+scale d*u) (y+scale d*v) := by
  unfold evenAffineGate at *
  simp only [scale,Nat.mul_assoc]
  omega
private theorem six_gate_lift {x y : Nat} (h : sixEvenRightGate x y) (d u v : Nat) :
    sixEvenRightGate (x+scale d*u) (y+scale d*v) := by
  unfold sixEvenRightGate at *
  simp only [scale,Nat.mul_assoc]
  omega
private theorem bad_lift {x y : Nat} (h : bad x y) (d u v : Nat) :
    bad (x+scale d*u) (y+scale d*v) := by
  unfold bad at *
  simp only [scale,Nat.mul_assoc]
  omega

private theorem lift_x_two (x y b u v c : Nat) (h : c≤x+y) :
    (x+4*b*u+(y+4*b*v)-c)/2 = (x+y-c)/2+b*(2*u+2*v) := by
  simp only [Nat.mul_assoc, Nat.mul_add, Nat.mul_left_comm b 2]
  omega
private theorem lift_y_two (x y b u v c : Nat) (h : c≤x+3*y) :
    (x+4*b*u+3*(y+4*b*v)-c)/4 = (x+3*y-c)/4+b*(u+3*v) := by
  simp only [Nat.mul_assoc, Nat.mul_add, Nat.mul_left_comm b 3]
  omega
private theorem lift_x_one (x y b u v : Nat) (h : 2≤x+y) :
    x+2*b*u+(y+2*b*v)-2 = x+y-2+b*(2*u+2*v) := by
  simp only [Nat.mul_assoc,Nat.mul_add,Nat.mul_left_comm b 2]
  omega
private theorem lift_y_one (y b v : Nat) (h : 2≤y) :
    (y+2*b*v-2)/2 = (y-2)/2+b*v := by
  simp only [Nat.mul_assoc]
  omega

/-- Every rejected point gives an exact infinite rectangular dyadic cylinder,
    with a computable modulus from the original inverse itinerary. -/
theorem fullForcedExcluded_lift (x y : Nat) (h : fullForcedExcluded x y=true) (u v : Nat) :
    fullForcedExcluded (x+scale (precision x y)*u) (y+scale (precision x y)*v) = true := by
  generalize hz : x+2*y=z
  induction z using Nat.strongRecOn generalizing x y u v with
  | ind z ih =>
    by_cases hO : oddLowGate x y
    · let X := (x+y-4)/2
      let Y := (x+3*y-10)/4
      have hp : precision x y = precision X Y + 2 := by
        conv => lhs; unfold precision
        rw [dite_eq_left hO]
      have hc : fullForcedExcluded X Y = true := by
        rw [excluded_congr (odd_norm hO)] at h
        exact h
      have hlt : X+2*Y<z := by dsimp [X,Y]; unfold oddLowGate at hO; omega
      have hx : 4≤x+y := by unfold oddLowGate at hO; omega
      have hy : 10≤x+3*y := by unfold oddLowGate at hO; omega
      have ho := odd_gate_lift hO (precision x y) u v
      rw [excluded_congr (odd_norm ho), hp, scale_two,
        lift_x_two x y (scale (precision X Y)) u v 4 hx,
        lift_y_two x y (scale (precision X Y)) u v 10 hy]
      exact ih _ hlt X Y hc (2*u+2*v) (u+3*v) rfl
    · by_cases hS : evenSevenGate x y
      · let X := (x+y-5)/2
        let Y := (x+3*y-9)/4
        have hp : precision x y = precision X Y + 2 := by
          conv => lhs; unfold precision
          rw [dite_eq_right hO, dite_eq_left hS]
        have hc : fullForcedExcluded X Y = true := by
          rw [excluded_congr (seven_norm hS)] at h
          exact h
        have hlt : X+2*Y<z := by dsimp [X,Y]; unfold evenSevenGate at hS; omega
        have hx : 5≤x+y := by unfold evenSevenGate at hS; omega
        have hy : 9≤x+3*y := by unfold evenSevenGate at hS; omega
        have hs := seven_gate_lift hS (precision x y) u v
        rw [excluded_congr (seven_norm hs), hp, scale_two,
          lift_x_two x y (scale (precision X Y)) u v 5 hx,
          lift_y_two x y (scale (precision X Y)) u v 9 hy]
        exact ih _ hlt X Y hc (2*u+2*v) (u+3*v) rfl
      · by_cases hA : evenAffineGate x y
        · let X := x+y-2
          let Y := (y-2)/2
          have hp : precision x y = precision X Y + 1 := by
            conv => lhs; unfold precision
            rw [dite_eq_right hO,dite_eq_right hS,dite_eq_left hA]
          have hc : fullForcedExcluded X Y = true := by
            rw [excluded_congr (affine_norm hA)] at h
            exact h
          have hlt : X+2*Y<z := by dsimp [X,Y]; unfold evenAffineGate at hA; omega
          have hx : 2≤x+y := by unfold evenAffineGate at hA; omega
          have hy : 2≤y := by unfold evenAffineGate at hA; omega
          have ha := affine_gate_lift hA (precision x y) u v
          rw [excluded_congr (affine_norm ha), hp, scale_one,
            lift_x_one x y (scale (precision X Y)) u v hx,
            lift_y_one y (scale (precision X Y)) v hy]
          exact ih _ hlt X Y hc (2*u+2*v) v rfl
        · by_cases hE : sixEvenRightGate x y
          · let X := x+y-2
            let Y := (y-2)/2
            have hp : precision x y = precision X Y + 1 := by
              conv => lhs; unfold precision
              rw [dite_eq_right hO,dite_eq_right hS,dite_eq_right hA,dite_eq_left hE]
            have hc : fullForcedExcluded X Y = true := by
              rw [excluded_congr (six_norm hE)] at h
              exact h
            have hlt : X+2*Y<z := by dsimp [X,Y]; unfold sixEvenRightGate at hE; omega
            have hx : 2≤x+y := by unfold sixEvenRightGate at hE; omega
            have hy : 2≤y := by unfold sixEvenRightGate at hE; omega
            have he := six_gate_lift hE (precision x y) u v
            rw [excluded_congr (six_norm he), hp, scale_one,
              lift_x_one x y (scale (precision X Y)) u v hx,
              lift_y_one y (scale (precision X Y)) v hy]
            exact ih _ hlt X Y hc (2*u+2*v) v rfl
          · have hn : fullForcedNormalize x y=(x,y) := by
              conv => lhs; unfold fullForcedNormalize
              rw [dite_eq_right hO,dite_eq_right hS,dite_eq_right hA,dite_eq_right hE]
            unfold fullForcedExcluded at h
            rw [hn] at h
            have hb : bad x y := by unfold bad; exact of_decide_eq_true h
            exact excluded_of_bad (bad_lift hb (precision x y) u v)

theorem blank_unreachable_lift (x y : Nat) (h : fullForcedExcluded x y=true) (u v time : Nat) :
    BB6.Agent8Section.run BB6.Agent46.secNext time (some (5,1)) ≠
      some (x+scale (precision x y)*u,y+scale (precision x y)*v) :=
  fullForcedExcluded_sound _ _ (fullForcedExcluded_lift x y h u v) time

#print axioms fullForcedExcluded_lift
#print axioms blank_unreachable_lift
end BB6.Agent12ForcedCylinder
