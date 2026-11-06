import Std
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace NeedleVariableValuation

def val (s : Nat) : Nat := (9^s+3)/2

theorem pow9_odd (s : Nat) : (9^s)%2 = 1 := by
  induction s with
  | zero => decide
  | succ s ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih]


theorem val_spec (s : Nat) : 2*val s = 9^s+3 := by
  have h := pow9_odd s
  unfold val
  omega

/-- The polynomial geometric factor of x^(2s) - 9^s. -/
def geometric (x : Nat) : Nat → Nat
  | 0 => 0
  | s+1 => x^(2*s)+9*geometric x s

theorem geom_identity (x s : Nat) :
    x^(2*s) + 9*geometric x s = x^2*geometric x s + 9^s := by
  induction s with
  | zero => simp [geometric]
  | succ s ih =>
    simp only [geometric]
    rw [show 2*(s+1)=2*s+2 by omega, Nat.pow_add]
    rw [show 9^(s+1)=9^s*9 by rw [Nat.pow_succ]]
    let A := x^(2*s)
    let X := x^2
    let T := geometric x s
    have h : A+9*T=X*T+9^s := ih
    change A*X+9*(A+9*T) = X*(A+9*T)+9^s*9
    calc
      A*X+9*(A+9*T) = A*X+9*(X*T+9^s) := by rw [h]
      _ = X*(A+9*T)+9^s*9 := by
        simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        omega

end NeedleVariableValuation

namespace NeedleVariableValuation

theorem square_difference (x : Nat) (h : 3 ≤ x) :
    (x+3)*(x-3)+9 = x^2 := by
  let y := x-3
  have hx : x=y+3 := by dsimp [y]; omega
  rw [hx]
  have hy : y+3-3=y := by omega
  rw [hy]
  simp only [Nat.pow_two, Nat.add_mul, Nat.mul_add]
  omega

theorem geometric_factor (x s : Nat) (hx : 3 ≤ x) :
    x^(2*s) = (x+3)*((x-3)*geometric x s)+9^s := by
  have hg := geom_identity x s
  have hm : x^2*geometric x s =
      (x+3)*((x-3)*geometric x s)+9*geometric x s := by
    calc
      x^2*geometric x s = ((x+3)*(x-3)+9)*geometric x s := by
        rw [square_difference x hx]
      _ = (x+3)*((x-3)*geometric x s)+9*geometric x s := by
        simp [Nat.add_mul, Nat.mul_assoc]
  rw [hm] at hg
  omega

theorem positive_power_mod2 (x n : Nat) (hx : x%2=0) :
    x^(n+1)%2=0 := by
  rw [Nat.pow_succ, Nat.mul_mod,hx]
  simp

theorem geometric_odd (x n : Nat) (hx : x%2=0) :
    geometric x (n+1)%2=1 := by
  induction n with
  | zero => simp [geometric]
  | succ n ih =>
    change (x^(2*(n+1))+9*geometric x (n+1))%2=1
    have hp : x^(2*(n+1))%2=0 := by
      rw [show 2*(n+1)= (2*n+1)+1 by omega]
      exact positive_power_mod2 x (2*n+1) hx
    rw [Nat.add_mod, Nat.mul_mod, hp, ih]


/-- An explicit unbounded-valuation family of legal incoming terminal edges. -/
theorem terminal_variable_valuation (t : Nat) :
    ∃ q v K : Nat,
      2*v=9^(t+1)+3 ∧
      K+1=2*(t+1)*(v+1) ∧
      2^K=(2^(v+1)+3)*q + 3*2^v+v+3 := by
  let s := t+1
  let v := val s
  let x := 2^(v+1)
  let g := geometric x s
  let P := (x-3)*g
  let q := (P-3)/2
  let K := (2*s*(v+1))-1
  have hv : 2*v=9^s+3 := val_spec s
  have hv2 : 2≤v := by
    have hp := Nat.pow_pos (by decide : 0<(9:Nat)) (n:=s)
    omega
  have hX : 8≤x := by
    have h := Nat.pow_le_pow_right (by decide : 0<(2:Nat))
        (show 3≤v+1 by omega)
    change 2^3≤x at h
    omega
  have hxEven : x%2=0 := by
    dsimp [x]
    rw [Nat.pow_succ, Nat.mul_mod]
    omega
  have hgOdd : g%2=1 := by
    change geometric x (t+1)%2=1
    exact geometric_odd x t hxEven
  have hg : 1≤g := by omega
  have hPbound : 3≤P := by
    have hmul := Nat.mul_le_mul_left (x-3) hg
    change (x-3)*1 ≤ P at hmul
    omega
  have hPodd : P%2=1 := by
    have hxOdd : (x-3)%2=1 := by omega
    dsimp [P]
    rw [Nat.mul_mod, hxOdd, hgOdd]
  have hq : 2*q+3=P := by dsimp [q]; omega
  have hKpositive : 0<2*s*(v+1) :=
    Nat.mul_pos (Nat.mul_pos (by decide) (by dsimp [s]; omega)) (by omega)
  have hK : K+1=2*s*(v+1) := by dsimp [K]; omega
  have hgeom : x^(2*s)=(x+3)*P+9^s := geometric_factor x s (by omega)
  have hpow : 2^(K+1)=x^(2*s) := by
    rw [hK, Nat.pow_mul' 2 (2*s) (v+1)]
  have hsource2 :
      2*((x+3)*q+3*2^v+v+3)=(x+3)*(2*q+3)+9^s := by
    have hx : x=2*2^v := by dsimp [x]; rw [Nat.pow_succ]; omega
    have hmul : (x+3)*(2*q) = 2*((x+3)*q) := by
      simp only [Nat.mul_left_comm]
    rw [Nat.mul_add (x+3) (2*q) 3, hmul]
    simp only [Nat.mul_add]
    omega
  have hgoal : 2^K=(2^(v+1)+3)*q+3*2^v+v+3 := by
    have he : 2^(K+1)=2*(2^K) := by rw [Nat.pow_succ]; omega
    change 2^K=(x+3)*q+3*2^v+v+3
    rw [hpow,hgeom,←hq] at he
    omega
  exact ⟨q,v,K,hv,hK,hgoal⟩

theorem valuation_unbounded (t : Nat) :
    ∃ q v K : Nat,
      t < v ∧
      2*v=9^(t+1)+3 ∧
      K+1=2*(t+1)*(v+1) ∧
      2^K=(2^(v+1)+3)*q + 3*2^v+v+3 := by
  have power_bound (s : Nat) : 2*s ≤ 9^s := by
    induction s with
    | zero => decide
    | succ s ih =>
      rw [Nat.pow_succ]
      have hp := Nat.pow_pos (by decide : 0<(9:Nat)) (n:=s)
      omega
  obtain ⟨q,v,K,hv,hK,he⟩ := terminal_variable_valuation t
  have hp := power_bound (t+1)
  exact ⟨q,v,K,by omega,hv,hK,he⟩

#print axioms terminal_variable_valuation
#print axioms valuation_unbounded

end NeedleVariableValuation
