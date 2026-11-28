import Anti3Core
import ReturnGCD
set_option maxHeartbeats 0

namespace BB6.Agent9Anti3
open BB6.Agent9ReturnGCD

/-- Modulus-three carries confined to a boundary force a constant selected
    bit throughout the available word. -/
theorem boundary_lock (a x : Nat → Int) (A B : Nat) (z : Int)
    (hz : z=0 ∨ z=3) (hstart : a A=z)
    (hx : ∀ j<A+B, x j=0 ∨ x j=1)
    (hs : ∀ j<A+B, 2*a (j+1)=a j+3*x j) :
    ∀ j<B, x (A+j)=z/3 := by
  have h : ∀ j≤B, a (A+j)=z := by
    intro j hj
    induction j with
    | zero => simpa using hstart
    | succ j ih =>
      have hp := ih (by omega)
      have hstep := hs (A+j) (by omega)
      have hb := hx (A+j) (by omega)
      rw [show A+(j+1)=A+j+1 by omega] 
      rcases hz with hz0|hz3
      · rcases hb with hb0|hb1
        · omega
        · omega
      · rcases hb with hb0|hb1
        · omega
        · omega
  intro j hj
  have hp := h j (by omega)
  have hn := h (j+1) (by omega)
  have hs' := hs (A+j) (by omega)
  rw [show A+(j+1)=A+j+1 by omega] at hn
  rcases hz with rfl|rfl <;> omega

/-- General source-ready obstruction for slope three. The two trace
    coordinates use opposite selected bits and the same affine clock. -/
theorem no_small_three_slope (q dir C : Int) (A B L : Nat)
    (a c w x : Nat → Int)
    (hdir : dir=1 ∨ dir= -1) (hL : A+B+1≤L)
    (hinit : -(2:Int)^A<a 0 ∧ a 0<3+(2:Int)^A)
    (hx : ∀ j<L, x j=0 ∨ x j=1)
    (ha : ∀ j<L, 2*a (j+1)=a j+3*x j)
    (hc : ∀ j<L, 2*c (j+1)=c j+(q+dir*(j:Int))*x j)
    (hw : ∀ j<L, 2*w (j+1)=w j+(q+dir*(j:Int))*(1-x j))
    (hbound : ∀ j≤L, 1≤c j ∧ c j≤C ∧ 1≤w j ∧ w j≤C)
    (hscale : 3*(C+1)<(2:Int)^B) : False := by
  have hconf := slope_confined 3 a x A (by decide)
    (fun j hj => hx j (by omega))
    (fun j hj => ha j (by omega)) hinit
  have hcB : C < (2:Int)^B := by
    have hC := hbound 0 (by omega)
    omega
  have hcases : a A=0 ∨ a A=1 ∨ a A=2 ∨ a A=3 := by omega
  rcases hcases with h0|h1|h2|h3
  · have hlock := boundary_lock a x A B 0 (Or.inl rfl) h0
      (fun j hj => hx j (by omega)) (fun j hj => ha j (by omega))
    apply no_positive_halves (fun j => c (A+j)) B
    · intro j hj
      have h := hc (A+j) (by omega)
      have he := hlock j hj
      simp at he
      rw [he] at h
      simpa only [Nat.add_assoc, Int.mul_zero, Int.add_zero] using h
    · exact (hbound (A+B) (by omega)).1
    · simpa using Int.lt_of_le_of_lt (hbound A (by omega)).2.1 hcB
  · apply no_anti3_interior (q+dir*(A:Int)) dir C B (L-A)
      (fun j => a (A+j)) (fun j => c (A+j)) (fun j => w (A+j))
      (fun j => x (A+j)) hdir (by omega) (Or.inl h1)
    · intro j hj; exact hx (A+j) (by omega)
    · intro j hj; simpa only [Nat.add_assoc] using ha (A+j) (by omega)
    · intro j hj
      have h := hc (A+j) (by omega)
      simpa only [Nat.add_assoc,Int.natCast_add,Int.mul_add,
        Int.add_assoc,Int.add_left_comm,Int.add_comm] using h
    · intro j hj
      have h := hw (A+j) (by omega)
      simpa only [Nat.add_assoc,Int.natCast_add,Int.mul_add,
        Int.add_assoc,Int.add_left_comm,Int.add_comm] using h
    · intro j hj; exact hbound (A+j) (by omega)
    · exact hscale
  · apply no_anti3_interior (q+dir*(A:Int)) dir C B (L-A)
      (fun j => a (A+j)) (fun j => c (A+j)) (fun j => w (A+j))
      (fun j => x (A+j)) hdir (by omega) (Or.inr h2)
    · intro j hj; exact hx (A+j) (by omega)
    · intro j hj; simpa only [Nat.add_assoc] using ha (A+j) (by omega)
    · intro j hj
      have h := hc (A+j) (by omega)
      simpa only [Nat.add_assoc,Int.natCast_add,Int.mul_add,
        Int.add_assoc,Int.add_left_comm,Int.add_comm] using h
    · intro j hj
      have h := hw (A+j) (by omega)
      simpa only [Nat.add_assoc,Int.natCast_add,Int.mul_add,
        Int.add_assoc,Int.add_left_comm,Int.add_comm] using h
    · intro j hj; exact hbound (A+j) (by omega)
    · exact hscale
  · have hlock := boundary_lock a x A B 3 (Or.inr rfl) h3
      (fun j hj => hx j (by omega)) (fun j hj => ha j (by omega))
    apply no_positive_halves (fun j => w (A+j)) B
    · intro j hj
      have h := hw (A+j) (by omega)
      have he := hlock j hj
      have he1 : (3:Int)/3=1 := by decide
      rw [he1] at he
      rw [he] at h
      simpa only [Nat.add_assoc, Int.sub_self, Int.mul_zero, Int.add_zero] using h
    · exact (hbound (A+B) (by omega)).2.2.1
    · simpa using Int.lt_of_le_of_lt (hbound A (by omega)).2.2.2 hcB

#print axioms boundary_lock
#print axioms no_small_three_slope
end BB6.Agent9Anti3
