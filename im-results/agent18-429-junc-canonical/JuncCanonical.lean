import High2PhysicalBridge
import Lean.Elab.Tactic.Omega

namespace BB429JuncCanonical

open BB6Coverage BB6Bubble BB429PhysicalFrontier BB429JPhysical
open BB429OddExcursion BB429SourceE1Return BB429FinishScanEDelta
open BB429PhysicalBridge

private theorem ones_getD (n j : Nat) :
    (ones n).getD j false = decide (j < n) := by
  induction n generalizing j with
  | zero => simp [ones]
  | succ n ih =>
    cases j with
    | zero => simp [ones]
    | succ j =>
      simpa [ones, List.replicate_succ] using ih j

private theorem pairs01_getD (n j : Nat) :
    (pairs01 n).getD j false = decide (j < 2*n ∧ j%2=1) := by
  induction n generalizing j with
  | zero => simp [pairs01]
  | succ n ih =>
    cases j with
    | zero => simp [pairs01]
    | succ j =>
      cases j with
      | zero => simp [pairs01]; omega
      | succ j =>
        change (pairs01 n).getD j false =
          decide (j+2 < 2*(n+1) ∧ (j+2)%2=1)
        rw [ih]
        have hp : (j < 2*n ∧ j%2=1) ↔
          (j+2 < 2*(n+1) ∧ (j+2)%2=1) := by omega
        simp only [hp]

private theorem getD_append {α : Type} (xs ys : List α) (j : Nat) (d : α) :
    (xs ++ ys).getD j d =
      if j < xs.length then xs.getD j d else ys.getD (j-xs.length) d := by
  induction xs generalizing j with
  | nil => simp
  | cons a xs ih =>
    cases j with
    | zero => simp
    | succ j => simpa using ih j

private theorem left_getD (u j : Nat) :
    (true :: (pairs01 u ++ ones 5)).getD j false =
      decide (j < 2*u+6 ∧ (2*u ≤ j ∨ j%2=0)) := by
  cases j with
  | zero => simp [ones]
  | succ j =>
    simp only [List.getD_cons_succ]
    rw [getD_append]
    have hlen : (pairs01 u).length = 2*u := by
      induction u with
      | zero => rfl
      | succ u ih => simp [pairs01, ih]; omega
    rw [hlen]
    rw [pairs01_getD,ones_getD]
    by_cases hj : j < 2*u
    · have hp : (j<2*u ∧ j%2=1) ↔
        (j+1<2*u+6 ∧ (2*u≤j+1 ∨ (j+1)%2=0)) := by omega
      simp only [if_pos hj]
      simp only [hp]
    · have hp : (j-2*u<5) ↔
        (j+1<2*u+6 ∧ (2*u≤j+1 ∨ (j+1)%2=0)) := by omega
      simp only [if_neg hj]
      simp only [hp]

private theorem tail_getD (k : Nat) :
    ([false,true] : List Bool).getD k false = decide (k=1) := by
  cases k with
  | zero => rfl
  | succ k => cases k <;> rfl

private theorem right_getD (w j : Nat) :
    (true :: (ones w ++ [false,true])).getD j false =
      decide (j ≤ w ∨ j=w+2) := by
  cases j with
  | zero => simp
  | succ j =>
    simp only [List.getD_cons_succ]
    rw [getD_append]
    have hlen : (ones w).length = w := by simp [ones]
    rw [hlen, ones_getD]
    by_cases hj : j<w
    · have hp : (j<w) ↔ (j+1≤w ∨ j+1=w+2) := by omega
      simp only [if_pos hj]
      simp only [hp]
    · have hp : (j-w=1) ↔ (j+1≤w ∨ j+1=w+2) := by omega
      simp only [if_neg hj]
      rw [tail_getD]
      simp only [hp]

private theorem jTape_center (u w : Nat) : jTape u w 0 = true := by
  have hh : jMark u w 0 := by
    unfold jMark jHole
    omega
  simp [jTape,hh]

private theorem jTape_left (u w j : Nat) :
    jTape u w (-((j:Int)+1)) =
      decide (j < 2*u+6 ∧ (2*u ≤ j ∨ j%2=0)) := by
  have hh : jMark u w (-((j:Int)+1)) ↔
      j < 2*u+6 ∧ (2*u ≤ j ∨ j%2=0) := by
    unfold jMark jHole
    omega
  simp [jTape,hh]

private theorem jTape_right (u w j : Nat) :
    jTape u w ((j:Int)+1) =
      decide (j ≤ w ∨ j=w+2) := by
  have hh : jMark u w ((j:Int)+1) ↔
      (j ≤ w ∨ j=w+2) := by
    unfold jMark jHole
    omega
  simp [jTape,hh]

/-- Canonical physical J tape is exactly the finite zipper Junc(u,0,w).
    The proof is extensional on both entire infinite tape tails. -/
theorem canonical_junc_rep (u w : Nat) (h : Int) :
    Represents (junc u 0 w)
      {state:=A,head:=h,tape:=fun x => jTape u w (x-h)} := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simpa [junc, z] using jTape_center u w
  · intro j
    change jTape u w ((h-((j:Int)+1))-h) =
      (true :: (pairs01 u ++ ones 5)).getD j false
    have hj : (h-((j:Int)+1))-h = -((j:Int)+1) := by omega
    rw [hj,jTape_left,left_getD]
  · intro j
    change jTape u w ((h+((j:Int)+1))-h) =
      (true :: (ones w ++ [false,true])).getD j false
    have hj : (h+((j:Int)+1))-h = ((j:Int)+1) := by omega
    rw [hj,jTape_right,right_getD]

/-- Every cell of any physical configuration represented by Junc(u,0,w)
    agrees with the translated exact canonical J tape. -/
theorem represented_junc_cell (u w : Nat) (c : Config)
    (hrep : Represents (junc u 0 w) c) (x : Int) :
    c.tape x = jTape u w (x-c.head) := by
  rcases hrep with ⟨hs, hc, hl, hr⟩
  by_cases hx : x = c.head
  · rw [hx]
    simpa [junc, z, jTape_center] using hc
  · by_cases hlt : x < c.head
    · let j : Nat := Int.toNat (c.head-x-1)
      have hpos : 0 ≤ c.head - x - 1 := by omega
      have heq : x = c.head - ((j:Int)+1) := by dsimp [j]; omega
      have hdiff : x-c.head = -((j:Int)+1) := by omega
      calc
        c.tape x = c.tape (c.head-((j:Int)+1)) := by rw [heq]
        _ = (junc u 0 w).left.getD j false := hl j
        _ = decide (j<2*u+6 ∧ (2*u≤j ∨ j%2=0)) := left_getD u j
        _ = jTape u w (x-c.head) := by rw [hdiff,jTape_left]
    · let j : Nat := Int.toNat (x-c.head-1)
      have hpos : 0 ≤ x - c.head - 1 := by omega
      have heq : x = c.head + ((j:Int)+1) := by dsimp [j]; omega
      have hdiff : x-c.head = ((j:Int)+1) := by omega
      calc
        c.tape x = c.tape (c.head+((j:Int)+1)) := by rw [heq]
        _ = (junc u 0 w).right.getD j false := hr j
        _ = decide (j≤w ∨ j=w+2) := right_getD w j
        _ = jTape u w (x-c.head) := by rw [hdiff,jTape_right]

theorem represented_junc_state (u w : Nat) (c : Config)
    (hrep : Represents (junc u 0 w) c) : c.state = A := by
  have hs : c.state.val = (A : Fin 6).val := hrep.1
  exact Fin.ext hs

/-- A canonical J-family physical configuration translated to any
    absolute head coordinate, retaining the exact infinite tape. -/
def translatedJ (u w : Nat) (h : Int) : Config :=
  {state:=A,head:=h,tape:=fun x => jTape u w (x-h)}

/-- The zipper representation is extensionally *identical* to the
    translated canonical J configuration, at every physical tape cell. -/
theorem represented_junc_eq_translatedJ (u w : Nat) (c : Config)
    (hrep : Represents (junc u 0 w) c) :
    c = translatedJ u w c.head := by
  have hs : c.state = A := represented_junc_state u w c hrep
  have ht : c.tape = (fun x => jTape u w (x-c.head)) := by
    funext x
    exact represented_junc_cell u w c hrep x
  cases c with
  | mk state head tape =>
    change Config.mk state head tape =
      Config.mk A head (fun x=>jTape u w (x-head))
    change state = A at hs
    change tape = (fun x=>jTape u w (x-head)) at ht
    rw [hs,ht]

theorem represented_junc_iff_translatedJ (u w : Nat) (c : Config) :
    Represents (junc u 0 w) c ↔ c = translatedJ u w c.head := by
  constructor
  · exact represented_junc_eq_translatedJ u w c
  · intro hc
    rw [hc]
    exact canonical_junc_rep u w c.head

#print axioms canonical_junc_rep
#print axioms represented_junc_cell
#print axioms represented_junc_state
#print axioms represented_junc_eq_translatedJ
#print axioms represented_junc_iff_translatedJ

end BB429JuncCanonical
