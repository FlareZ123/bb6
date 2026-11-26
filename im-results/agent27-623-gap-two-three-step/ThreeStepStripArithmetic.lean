import Lean.Elab.Tactic.Omega
namespace BB6.Agent27ThreeStepStripArithmetic

def strip (u v n : Nat) : Prop :=
  let m := min u v
  let L := max u v
  let E := 35*n+93
  (L ≤ 13*m+E ∧ 13*m ≤ L+E) ∨
  (4*L ≤ 7*m+E ∧ 7*m ≤ 4*L+E)

theorem scale_growth (n : Nat) (hn : 10 ≤ n) : 100*n+500 ≤ 3^n := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => decide
  | succ k ih =>
      have hp : 3^(10+(k+1)) = 3 * 3^(10+k) := by
        rw [← Nat.add_assoc, Nat.pow_succ]
        omega
      omega

theorem scale_growth9 (n : Nat) (hn : 9 ≤ n) : 100*n+403 ≤ 3^n := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => decide
  | succ k ih =>
      have hp : 3^(9+(k+1)) = 3 * 3^(9+k) := by
        rw [← Nat.add_assoc, Nat.pow_succ]
        omega
      omega

theorem band_growth (n m : Nat) (hn : 10 ≤ n)
    (hm : 3^(n-1)-3 ≤ m) : 100*n+300 ≤ m := by
  have h := scale_growth9 (n-1) (by omega)
  omega

theorem terminal_scale (n m x y : Nat) (hn : 10 ≤ n)
    (hm : m+3 < 3^n) (hy : y ≤ 3*m+6*n+9)
    (hx : x ≤ 16*y+68) :
    y+3 < 3^(n+2) ∧ 2*(x+y+x+y+10+3*(n+2))+5 < 3^(n+5) := by
  have h := scale_growth n hn
  have h2 : 3^(n+2) = 9*3^n := by rw [Nat.pow_add]; omega
  have h5 : 3^(n+5) = 243*3^n := by rw [Nat.pow_add]; omega
  omega

/-- The far-oriented previous branch needs no ordering transfer. -/
theorem far_cancel (n u v x y : Nat) (huv : v ≤ u)
    (hleft : -(26*n+46 : Int) ≤ (x:Int)-4*(y:Int)-5-((u:Int)-13*(v:Int)) ∧
      (x:Int)-4*(y:Int)-5-((u:Int)-13*(v:Int)) ≤ (26*n+46 : Int))
    (hright : -(26*n+46 : Int) ≤ (y:Int)-4*(x:Int)-1-(7*(v:Int)-4*(u:Int)) ∧
      (y:Int)-4*(x:Int)-1-(7*(v:Int)-4*(u:Int)) ≤ (26*n+46 : Int))
    (hterm : (4*y ≤ x+9*n+38 ∧ x ≤ 4*y+9*n+38) ∨
      (4*x ≤ y+9*n+38 ∧ y ≤ 4*x+9*n+38)) : strip u v n := by
  unfold strip
  simp only [Nat.min_eq_right huv,Nat.max_eq_left huv]
  rcases hterm with h | h
  · left; omega
  · right; omega

/-- The near branch can cross the diagonal by up to four. The scale lower
bound forces the intended ordering once either cancellation occurs. -/
theorem near_cancel (n u v x y : Nat) (hn : 10 ≤ n)
    (hm : 3^(n-1)-3 ≤ min u v)
    (hleft : -(26*n+46 : Int) ≤ (x:Int)-4*(y:Int)-5-((v:Int)-13*(u:Int)) ∧
      (x:Int)-4*(y:Int)-5-((v:Int)-13*(u:Int)) ≤ (26*n+46 : Int))
    (hright : -(26*n+46 : Int) ≤ (y:Int)-4*(x:Int)-1-(7*(u:Int)-4*(v:Int)) ∧
      (y:Int)-4*(x:Int)-1-(7*(u:Int)-4*(v:Int)) ≤ (26*n+46 : Int))
    (hterm : (4*y ≤ x+9*n+38 ∧ x ≤ 4*y+9*n+38) ∨
      (4*x ≤ y+9*n+38 ∧ y ≤ 4*x+9*n+38)) : strip u v n := by
  have hg := band_growth n (min u v) hn hm
  have huv : u ≤ v := by
    by_cases h : u ≤ v
    · exact h
    · have h' : v ≤ u := by omega
      rw [Nat.min_eq_right h'] at hg
      rcases hterm with h | h <;> omega
  unfold strip
  simp only [Nat.min_eq_left huv,Nat.max_eq_right huv]
  rcases hterm with h | h
  · left; omega
  · right; omega

#print axioms terminal_scale
#print axioms far_cancel
#print axioms near_cancel
end BB6.Agent27ThreeStepStripArithmetic
