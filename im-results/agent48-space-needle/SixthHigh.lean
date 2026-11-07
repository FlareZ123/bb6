import FifthHigh
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
namespace BB6.Agent48.SixthHigh
open BB6.Agent48.FifthHigh

theorem five_poly (x y : Nat) :
    y*x^5 +243*y + (x+3)*(y*(3*x^3+27*x)) =
    (x+3)*(y*(x^4+9*x^2+81)) := by
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.one_mul]
  simp [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  ac_rfl

private theorem high_power (v s : Nat) :
    2*(2:Nat)^(5*v+4+s)=(2:Nat)^s*((2:Nat)^(v+1))^5 := by
  have h : 5*v+5+s=s+5*(v+1) := by omega
  have hp : 2*(2:Nat)^(5*v+4+s)=(2:Nat)^(5*v+5+s) := by
    have ht : 5*v+5+s=(5*v+4+s)+1 := by omega
    rw [ht,Nat.pow_succ']
  rw [hp,h,Nat.pow_add]
  have ht : (2:Nat)^(5*(v+1))=((2:Nat)^(v+1))^5 := by
    rw [Nat.mul_comm 5 (v+1),Nat.pow_mul]
  rw [ht]

private theorem high_mod (q v s : Nat)
    (heq : equation q v (5*v+4+s)) :
    (2*v+243*(2:Nat)^s)%den v=3%den v := by
  let x : Nat := (2:Nat)^(v+1)
  let z : Nat := (2:Nat)^v
  let y : Nat := (2:Nat)^s
  let D : Nat := x+3
  have hx : x=2*z := by dsimp [x,z]; rw [Nat.pow_succ']
  have hp : 2*(2:Nat)^(5*v+4+s)=y*x^5 := by
    simpa only [x,y] using high_power v s
  have he0 : D*q+3*z+v+3=(2:Nat)^(5*v+4+s) := by
    simpa only [equation,den,bias,D,x,z,Nat.add_assoc] using heq
  have he : y*x^5=D*(2*q)+3*x+2*v+6 := by
    rw [←hp,←he0,hx]
    simp only [Nat.mul_add]
    simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  have hpoly : y*x^5+243*y+D*(y*(3*x^3+27*x)) =
      D*(y*(x^4+9*x^2+81)) := by
    simpa only [D] using five_poly x y
  have hcore : D*(2*q+3+y*(3*x^3+27*x))+(2*v+243*y) =
      D*(y*(x^4+9*x^2+81))+3 := by
    calc
      _ = y*x^5+243*y+D*(y*(3*x^3+27*x))+3 := by
        rw [he]
        simp only [Nat.mul_add]
        omega
      _ = D*(y*(x^4+9*x^2+81))+3 := by rw [hpoly]
  have hm := congrArg (fun a : Nat => a%D) hcore
  have hmod : (2*v+243*y)%D=3%D := by
    simpa [Nat.add_mod,Nat.mul_mod] using hm
  simpa only [den,x,y,D] using hmod

private theorem double_le_pow (v : Nat) (hv : 2≤v) :
    2*v≤(2:Nat)^v := by
  have h : ∀ n : Nat, 2*(2+n) ≤ (2:Nat)^(2+n) := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
      have hp : 2 ≤ (2:Nat)^(2+n) := by
        have hh := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega : 1≤2+n)
        simpa using hh
      have he : (2:Nat)^(2+(n+1))=2*((2:Nat)^(2+n)) := by
        have hh : 2+(n+1)=(2+n)+1 := by omega
        rw [hh,Nat.pow_succ']
      rw [he]
      omega
  have ha : 2+(v-2)=v := by omega
  simpa only [ha] using h (v-2)

/-- Every high-side source is within eight valuations of its fifth-power wall. -/
theorem high_sixth_bound (q v s : Nat)
    (heq : equation q v (5*v+4+s)) : v≤s+8 := by
  by_cases hv : v≤s+8
  · exact hv
  · have hvlarge : s+9≤v := by omega
    have h2v : 2*v≤(2:Nat)^v := double_le_pow v (by omega)
    have he : (2:Nat)^(s+9)≤(2:Nat)^v :=
      Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hvlarge
    have hs : (2:Nat)^(s+9)=512*(2:Nat)^s := by
      have hh : s+9=9+s := by omega
      rw [hh,Nat.pow_add]
    rw [hs] at he
    have h243 : 243*(2:Nat)^s ≤ (2:Nat)^v := by
      have hsmall := Nat.mul_le_mul_right ((2:Nat)^s) (by decide : 243≤512)
      omega
    have hpow : (2:Nat)^(v+1)=2*((2:Nat)^v) := by rw [Nat.pow_succ']
    have hD : 2*v+243*(2:Nat)^s < den v := by
      unfold den
      rw [hpow]
      omega
    have h3 : 3<den v := by
      unfold den
      have hh : 0<(2:Nat)^(v+1) := Nat.pow_pos (by decide)
      omega
    have hm:=high_mod q v s heq
    rw [Nat.mod_eq_of_lt hD,Nat.mod_eq_of_lt h3] at hm
    have hy : 0<(2:Nat)^s := Nat.pow_pos (by decide)
    omega

#print axioms high_sixth_bound
end BB6.Agent48.SixthHigh
