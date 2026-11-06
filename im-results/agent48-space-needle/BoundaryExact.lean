import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
namespace BB6.Agent48.Boundary

def den (v : Nat) := (2:Nat)^(v+1)+3
def bias (v : Nat) := 3*(2:Nat)^v+v+3
def equation (q v K : Nat) : Prop := den v*q+bias v=(2:Nat)^K

theorem model_eq (q v : Nat) :
  den v*q+bias v = (2:Nat)^v*(2*q+3)+v+3*(q+1) := by
  simp [den,bias,Nat.pow_succ,Nat.mul_add,Nat.add_mul, Nat.mul_assoc, Nat.mul_comm]
  ac_rfl

private theorem cube_identity (x : Nat) :
  (x+3)*(2*x*x+18) = 2*(x*x*x)+54+6*x*(x+3) := by
  simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  ac_rfl

private theorem cube_power (v : Nat) :
   (2:Nat)^(3*v+3)= ((2:Nat)^(v+1))*((2:Nat)^(v+1))*((2:Nat)^(v+1)) := by
  have hexp : 3*v+3=(v+1)*3 := by omega
  rw [hexp, Nat.pow_mul]
  simp [Nat.pow_succ, Nat.pow_zero, Nat.mul_assoc]

private theorem two_power (v : Nat) : (2:Nat)^(v+1)=2*(2:Nat)^v := by
  rw [Nat.pow_succ]
  omega

private theorem boundary_divides (q v : Nat)
    (h : equation q v (3*v+3)) : den v ∣ 2*v+51 := by
  let x : Nat := (2:Nat)^(v+1)
  let z : Nat := (2:Nat)^v
  have hx : x=2*z := two_power v
  have hp : (2:Nat)^(3*v+3)=x*x*x := cube_power v
  have he : (x+3)*q+3*z+v+3=x*x*x := by
    simpa only [equation,den,bias,x,z,hp, Nat.add_assoc] using h
  have hr : 2*(x*x*x)+54=(x+3)*(2*q+3)+(2*v+51) := by
    calc
      2*(x*x*x)+54 = 2*((x+3)*q+3*z+v+3)+54 := by rw [he]
      _ = (x+3)*(2*q+3)+(2*v+51) := by
         simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
         omega
  have hbig : (x+3)*(2*x*x+18) = (x+3)*(2*q+3+6*x)+(2*v+51) := by
    calc
      (x+3)*(2*x*x+18) = 2*(x*x*x)+54+6*x*(x+3) := cube_identity x
      _ = (x+3)*(2*q+3)+(2*v+51)+6*x*(x+3) := by rw [hr]
      _ = (x+3)*(2*q+3+6*x)+(2*v+51) := by
        simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        omega
  have hBA : 2*q+3+6*x ≤ 2*x*x+18 := by
    have hpos : 0<x+3 := by omega
    by_cases hb : 2*q+3+6*x ≤ 2*x*x+18
    · exact hb
    · have hlt : 2*x*x+18 < 2*q+3+6*x := by omega
      have hm := Nat.mul_lt_mul_of_pos_left hlt hpos
      omega
  have hs : (2*q+3+6*x) + ((2*x*x+18)-(2*q+3+6*x))= 2*x*x+18 := by omega
  have hgap : 2*v+51 = (x+3)*((2*x*x+18)-(2*q+3+6*x)) := by
    have ha := congrArg (fun a : Nat => (x+3)*a) hs
    rw [Nat.mul_add] at ha
    omega
  refine ⟨(2*x*x+18)-(2*q+3+6*x), ?_⟩
  simpa only [den,x] using hgap

private theorem exponential_dominates (v : Nat) (hv : 5 ≤ v) :
  2*v+51 < den v := by
  have hbase : ∀ n : Nat, 2*(5+n)+51 < den (5+n) := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
      have he : 2 ≤ (2:Nat)^(5+n+1) := by
        have hp := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega : 1 ≤ 5+n+1)
        simpa using hp
      have hs : (2:Nat)^(5+(n+1)+1) = 2*((2:Nat)^(5+n+1)) := by
        have heq : 5+(n+1)+1 = (5+n+1)+1 := by omega
        rw [heq, Nat.pow_succ']
      simp only [den] at ih ⊢
      rw [hs]
      omega
  have hv' : 5+(v-5)=v := by omega
  simpa only [hv'] using hbase (v-5)

theorem terminal_threshold_exact (q v K : Nat)
    (h : equation q v K) (hK : K=3*v+3) :
    (q=45 ∧ v=2 ∧ K=9) ∨ (q=214 ∧ v=3 ∧ K=12) := by
  subst K
  have hdvd := boundary_divides q v h
  have hvlt : v < 5 := by
    by_cases hv : 5 ≤ v
    · have hd := exponential_dominates v hv
      have hle : den v ≤ 2*v+51 := Nat.le_of_dvd (by omega) hdvd
      omega
    · omega
  have hcases : v=0 ∨ v=1 ∨ v=2 ∨ v=3 ∨ v=4 := by omega
  rcases hcases with hv | hv | hv | hv | hv
  all_goals subst v <;> simp [equation,den,bias] at h ⊢ <;> omega

theorem terminal_threshold_iff (q v K : Nat) :
    equation q v K ∧ K=3*v+3 ↔
      (q=45 ∧ v=2 ∧ K=9) ∨ (q=214 ∧ v=3 ∧ K=12) := by
  constructor
  · rintro ⟨he,hK⟩
    exact terminal_threshold_exact q v K he hK
  · intro hh
    rcases hh with hh | hh
    · rcases hh with ⟨rfl,rfl,rfl⟩
      simp [equation,den,bias]
    · rcases hh with ⟨rfl,rfl,rfl⟩
      simp [equation,den,bias]

#print axioms model_eq
#print axioms terminal_threshold_iff
#print axioms terminal_threshold_exact
#print axioms boundary_divides
#print axioms exponential_dominates
end BB6.Agent48.Boundary
