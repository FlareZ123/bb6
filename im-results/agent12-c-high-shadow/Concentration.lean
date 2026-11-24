import Lean
namespace MachineCConcentration

theorem suffix_update_odd (r q : Nat) (hr : 1 ≤ r) :
    (2^r*q+1)%2=1 := by
  cases r with
  | zero => omega
  | succ r =>
    rw [Nat.pow_succ]
    have h : 2^r*2*q=2*(2^r*q) := by ac_rfl
    rw [h]
    omega

theorem recover_mass (R Q M1 M2 : Nat)
    (hodd : Q%2=1) (hle : M1≤M2) (hgap : M2-M1<2^R)
    (hdvd : 2^R ∣ Q*(M2-M1)) : M1=M2 := by
  have hc : Nat.Coprime 2 Q := by
    change Nat.gcd 2 Q = 1
    rw [Nat.gcd_rec,hodd]
    decide
  have h := (hc.pow_left R).dvd_of_dvd_mul_left hdvd
  by_cases he : M1=M2
  · exact he
  · have hpos : 0 < M2-M1 := by omega
    have := Nat.le_of_dvd hpos h
    omega

theorem endpoint_determines_mass (R Q M1 M2 A1 A2 : Nat) (C : Int)
    (hodd : Q%2=1) (hle : M1≤M2) (hgap : M2-M1<2^R)
    (heq : (2:Int)^R*(A1:Int)-(Q:Int)*(M1:Int)+C =
           (2:Int)^R*(A2:Int)-(Q:Int)*(M2:Int)+C) : M1=M2 := by
  apply recover_mass R Q M1 M2 hodd hle hgap
  have h : (Q:Int)*(↑(M2-M1):Int) = (2:Int)^R*((A2:Int)-(A1:Int)) := by
    rw [Int.ofNat_sub hle]
    grind
  rw [←Int.ofNat_dvd]
  push_cast
  exact ⟨(A2:Int)-(A1:Int),h⟩

#print axioms suffix_update_odd
#print axioms recover_mass
#print axioms endpoint_determines_mass
end MachineCConcentration
