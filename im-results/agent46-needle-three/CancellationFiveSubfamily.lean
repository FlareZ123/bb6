import CancellationTopStrip
import Lean.Elab.Tactic.Omega

namespace CancellationFive
open CancellationNat CancellationGap

private theorem cycle67 (a period n : Nat) (hc:(a^period)%67=1) :
    (a^n)%67=(a^(n%period))%67 := by
  have hr : period*(n/period)+n%period=n := by
    have hh := Nat.mod_add_div n period
    omega
  have hp : (a^(period*(n/period)))%67=1 := by
    rw [Nat.pow_mul, Nat.pow_mod, hc]
    simp
  calc
    (a^n)%67 = (a^(period*(n/period)+n%period))%67 := by rw [hr]
    _ = (a^(n%period))%67 := by
      rw [Nat.pow_add, Nat.mul_mod, hp]
      omega

private theorem nine_mod132 (n : Nat) : (9^(5*n+4))%132=93 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show 5*(n+1)+4=(5*n+4)+5 by omega, Nat.pow_add, Nat.mul_mod, ih]

private theorem valuation_mod66 (t:Nat) :
    (valuationA (214+495*t))%66=49 := by
  have hh := nine_mod132 (42+99*t)
  have he : 5*(42+99*t)+4=214+495*t := by omega
  rw [he] at hh
  unfold valuationA
  omega

private theorem A_mod67 (t:Nat) :
    (2^(valuationA (214+495*t)))%67=57 := by
  have hp := cycle67 2 66 (valuationA (214+495*t)) (by decide)
  rw [valuation_mod66 t] at hp
  exact hp.trans (by decide)

private theorem r_mod33 (t:Nat) : (214+495*t)%33=16 := by omega
private theorem r_mod11 (t:Nat) : (214+495*t)%11=5 := by omega

/-- A third, independent legal immediate-parent valuation is present at
    every cancellation feeder in the infinite index progression 214+495t. -/
theorem val_five_subfamily (t:Nat) :
    67 ∣ (2^(valuationA (214+495*t))*
       P (2^(valuationA (214+495*t))) (214+495*t)+3-10) := by
  let r:=214+495*t
  let A:=2^(valuationA r)
  let Q:=P A r
  have hr : 1≤r := by dsimp [r]; omega
  have hA : A%67=57 := A_mod67 t
  have ha : 4≤valuationA r := by
    have hp : (9:Nat)^1≤9^r := Nat.pow_le_pow_right (by decide) hr
    dsimp [valuationA]
    omega
  have hA3 : 3≤A := by
    have h := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) ha
    dsimp [A]
    omega
  have heq : (A+3)*Q+9^r=A^(2*r) := CancellationNat.exact A r hA3
  have hSquare : (A*A)%67=33 := by rw [Nat.mul_mod,hA]
  have hPower : (A^(2*r))%67=47 := by
    have hp : (A^(2*r))%67=((A*A)^r)%67 := by
      rw [Nat.pow_mul]
      simp only [Nat.pow_succ]
      simp
    rw [hp]
    have hpcycle : ((A*A)^r)%67=(33^r)%67 := by
      calc
        ((A*A)^r)%67=(((A*A)%67)^r)%67 := Nat.pow_mod (A*A) r 67
        _ = (33^r)%67 := by rw [hSquare]
    rw [hpcycle, cycle67 33 33 r (by decide), r_mod33 t]
  have hNine : (9^r)%67=22 := by
    rw [cycle67 9 11 r (by decide), r_mod11 t]
  have hQmod : Q%67=6 := by
    have hm := congrArg (fun x:Nat=>x%67) heq
    have hAsum : (A+3)%67=60 := by omega
    rw [Nat.add_mod,Nat.mul_mod,hAsum,hNine,hPower] at hm
    omega
  have hAPmod : (A*Q)%67=7 := by
    rw [Nat.mul_mod,hA,hQmod]
  have hQpositive : 0<Q := CancellationStrip.P_pos A r (by omega) hr
  have hAPpos : 10≤A*Q+3 := by
    have hh : A≤A*Q := Nat.le_mul_of_pos_right A hQpositive
    omega
  have hd : (A*Q+3-10)%67=0 := by omega
  exact Nat.dvd_of_mod_eq_zero hd

#print axioms val_five_subfamily
end CancellationFive
