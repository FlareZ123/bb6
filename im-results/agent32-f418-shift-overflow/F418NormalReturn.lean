import F418Episodes
import F418ReturnBounds

namespace BB6.Agent32F418.ReturnBounds
open Arithmetic EventSystem State

namespace Prefix

def steps : Prefix → Nat
  | last _ => 1
  | more _ t => t.steps+1

theorem value_pos (b : Prefix) (Q : Nat) : 0 < b.value Q := by
  have h := (value_bounds b Q).1
  omega

theorem reset1_affine (j n e : Nat) :
    resetRight 1 (n+(2^j-1)) e =
      n*2^(e+2)+(2^(j+2)-1)*2^e := by
  unfold resetRight
  have hx := Nat.two_pow_pos j
  have hp : 2^(j+2)=4*2^j := by rw [Nat.pow_add,Nat.mul_comm]
  have h : 4*(n+(2^j-1))+1+2*1 = 4*n+(2^(j+2)-1) := by rw [hp]; omega
  rw [h,Nat.add_mul,Nat.pow_add (a:=2) (m:=e) (n:=2)]
  change 4*n*2^e+(2^(j+2)-1)*2^e = n*(2^e*4)+(2^(j+2)-1)*2^e
  ac_rfl

theorem episode_exact (b : Prefix) (Q n w : Nat) :
    iterate b.steps (shift2 (b.value Q) 1 n w) =
      some (reg0 Q (n*2^b.E+b.C) (w+b.E)) := by
  induction b generalizing n w with
  | last r =>
    have hj : (2*r)%2=0 := by omega
    have he : (5*(2*r)+1)/2=5*r := by omega
    simp [steps,value,iterate,advance,splitOdd_factor,hj,he,reset1_affine,C,Nat.add_assoc]
  | more r t ih =>
    have hj : (2*r+1)%2≠0 := by omega
    have he : (5*(2*r+1)+1)/2=5*r+3 := by omega
    have hpos : t.value Q≠0 := Nat.ne_of_gt (value_pos t Q)
    simp only [steps,iterate,advance,value,splitOdd_factor,if_neg hj,he,shift2OrReg1,
      if_neg hpos,Option.bind_some]
    rw [ih, reset1_affine]
    simp only [C,E_more,Option.some.injEq,State.reg0.injEq]
    refine ⟨trivial,?_,?_⟩
    · rw [Nat.add_mul,Nat.mul_assoc n,←Nat.pow_add,Nat.mul_assoc (2^(2*r+1+2)-1),←Nat.pow_add]
      simp only [show 5*r+3+2+t.E=5*r+5+t.E by omega,
        show 2*r+1+2=2*r+3 by omega,Nat.add_assoc]
    · omega

theorem normal_return_exact (b : Prefix) (Q W : Nat) (hwidth : b.value Q < 2^W) :
    iterate (b.steps+1) (shift2 (b.value Q) 1 (2^W) (W+1)) =
      some (shift2 (b.next Q W) 1 (2^(W+b.E+1)) (W+b.E+2)) := by
  have hL := (width_tail hwidth).1
  have hc : b.C < 2^(W+b.E) :=
    Nat.lt_of_lt_of_le (correction_upper b) (pow_mono (by simp [L] at hL; omega))
  rw [iterate_add,episode_exact,←Nat.pow_add]
  simp only [Option.bind_some,iterate,advance,Option.some.injEq,State.shift2.injEq]
  simp only [gap,next]
  rw [show W+1+b.E=W+b.E+1 by omega,Nat.pow_succ 2 (W+b.E)]
  have h := Nat.two_pow_pos (W+b.E)
  simp only [and_true, true_and, Nat.add_assoc]
  omega

theorem seed_to_pure :
    iterate 4 seed = some (shift2 268311341 1 (2^29) 30) := by
  have h1 : splitOdd 26072 = (3,1629) := by
    rw [show 26072 = 2^3*(2*1629+1) by decide,splitOdd_factor]
  have h2 : splitOdd 1629 = (0,814) := by
    rw [show 1629 = 2^0*(2*814+1) by decide,splitOdd_factor]
  have a : advance seed = some (shift4 26072 15) := rfl
  have b : advance (shift4 26072 15) = some (shift2 1629 0 67140096 27) := by
    simp only [advance,h1]; decide
  have c : advance (shift2 1629 0 67140096 27) = some (reg0 814 268560385 29) := by
    simp only [advance,h2]; decide
  have d : advance (reg0 814 268560385 29) = some (shift2 268311341 1 (2^29) 30) := by decide
  simp only [iterate,a,b,c,d,Option.bind_some]

#print axioms episode_exact
#print axioms normal_return_exact
#print axioms seed_to_pure

end Prefix
end BB6.Agent32F418.ReturnBounds
