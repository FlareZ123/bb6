import Anti5Interior
import ReturnGCD
set_option maxHeartbeats 0
namespace BB6.Agent9Anti5
open BB6.Agent9ReturnGCD

/-- Modulus-five boundary slopes force a constant selected bit. -/
theorem boundary_lock5 (a x : Nat→Int) (A K : Nat) (z : Int)
    (hz : z=0∨z=5) (hstart : a A=z)
    (hx : ∀ j<A+K, x j=0∨x j=1)
    (hs : ∀ j<A+K, 2*a (j+1)=a j+5*x j) :
    ∀ j<K, x (A+j)=z/5 := by
  have h : ∀ j≤K, a (A+j)=z := by
    intro j hj
    induction j with
    | zero => simpa using hstart
    | succ j ih =>
      have hp := ih (by omega)
      have hs' := hs (A+j) (by omega)
      have hb := hx (A+j) (by omega)
      rw [show A+(j+1)=A+j+1 by omega]
      rcases hz with h0|h5 <;> rcases hb with hb0|hb1 <;> omega
  intro j hj
  have hp := h j (by omega)
  have hn := h (j+1) (by omega)
  have hs' := hs (A+j) (by omega)
  rw [show A+(j+1)=A+j+1 by omega] at hn
  rcases hz with rfl|rfl <;> omega

/-- Slope five has only boundary locks or a strictly-interior four-cycle;
    in the latter case the period-two anti-determinant excludes long words. -/
theorem no_small_five_slope (q dir C : Int) (A B L : Nat)
    (a c w x : Nat→Int)
    (hdir : dir=1∨dir= -1) (hL : A+2*B+2≤L)
    (hinit : -(2:Int)^A<a 0 ∧ a 0<5+(2:Int)^A)
    (hx : ∀ j<L, x j=0∨x j=1)
    (ha : ∀ j<L, 2*a (j+1)=a j+5*x j)
    (hc : ∀ j<L, 2*c (j+1)=c j+(q+dir*(j:Int))*x j)
    (hw : ∀ j<L, 2*w (j+1)=w j+(q+dir*(j:Int))*(1-x j))
    (hbound : ∀ j≤L, 1≤c j ∧ c j≤C ∧ 1≤w j ∧ w j≤C)
    (hscale : 5*(C+3)<(2:Int)^(2*B)) : False := by
  have hconf := slope_confined 5 a x A (by decide)
    (fun j hj => hx j (by omega))
    (fun j hj => ha j (by omega)) hinit
  have hcB : C<(2:Int)^(2*B) := by
    have hC := hbound 0 (by omega)
    omega
  by_cases h0 : a A=0
  · have hlock := boundary_lock5 a x A (2*B) 0 (Or.inl rfl) h0
      (fun j hj => hx j (by omega)) (fun j hj => ha j (by omega))
    apply no_positive_halves (fun j => c (A+j)) (2*B)
    · intro j hj
      have h := hc (A+j) (by omega)
      have he := hlock j hj
      simp at he
      rw [he] at h
      simpa only [Nat.add_assoc,Int.mul_zero,Int.add_zero] using h
    · exact (hbound (A+2*B) (by omega)).1
    · simpa using Int.lt_of_le_of_lt (hbound A (by omega)).2.1 hcB
  by_cases h5 : a A=5
  · have hlock := boundary_lock5 a x A (2*B) 5 (Or.inr rfl) h5
      (fun j hj => hx j (by omega)) (fun j hj => ha j (by omega))
    apply no_positive_halves (fun j => w (A+j)) (2*B)
    · intro j hj
      have h := hw (A+j) (by omega)
      have he := hlock j hj
      have he1 : (5:Int)/5=1 := by decide
      rw [he1] at he
      rw [he] at h
      simpa only [Nat.add_assoc,Int.sub_self,Int.mul_zero,Int.add_zero] using h
    · exact (hbound (A+2*B) (by omega)).2.2.1
    · simpa using Int.lt_of_le_of_lt (hbound A (by omega)).2.2.2 hcB
  have hinner : 1≤a A ∧ a A≤4 := by omega
  apply no_anti5_interior (q+dir*(A:Int)) dir C B (L-A)
    (fun j => a (A+j)) (fun j => c (A+j)) (fun j => w (A+j))
    (fun j => x (A+j)) hdir (by omega) hinner
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

#print axioms no_small_five_slope
end BB6.Agent9Anti5
