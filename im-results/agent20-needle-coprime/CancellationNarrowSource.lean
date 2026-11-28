import CancellationRotationBound
import CancellationNarrow

namespace NeedleRotation.Cancellation

theorem first_narrow_cutoff (r m : Nat) (hr : 8≤r) (hm : 0<m) (hmphys : m≤2*r*a r)
    (hd : denominator m∣value ((5-2*(m:Int),0)::sparse (a r) 1 (2*r))) :
    4*(m*m)<13*(r+1)*a r := by
  exact Asymmetric.narrow_cutoff r (N r) (a r) m 1 (5-2*(m:Int)) hr
    (a_growth r hr) (a_spec r) (N_ge_81 r (by omega)) (N_lt_pow r (by omega))
    hm (first_cutoff r m hr hm hmphys hd) (by decide) (by omega) (by omega)
    (sparse_to_three r m 1 (5-2*(m:Int)) hd)

theorem second_narrow_cutoff (j m : Nat) (hm : 0<m) (hmphys : m≤2*(110*j+50)*a (110*j+50))
    (hd : denominator m∣value ((325-110*(m:Int),0)::sparse (a (110*j+50)) 16 (2*(110*j+50)))) :
    4*(m*m)<13*((110*j+50)+1)*a (110*j+50) := by
  let r := 110*j+50
  have hr : 8≤r := by dsimp [r]; omega
  exact Asymmetric.narrow_cutoff r (N r) (a r) m 16 (325-110*(m:Int)) hr
    (a_growth r hr) (a_spec r) (N_ge_81 r (by omega)) (N_lt_pow r (by omega))
    hm (second_cutoff j m hm hmphys hd) (by decide) (by omega) (by omega)
    (sparse_to_three r m 16 (325-110*(m:Int)) hd)

/-- All-r>=8 cutoff, stated directly on the exact original-source parent
    equation for the constructed cancellation feeder. -/
theorem first_source_equation_narrow_cutoff (r P b q w : Nat) (hr : 8≤r)
    (hP : (2^(a r)+3)*P+N r=(2^(a r))^(2*r))
    (hb : 2*b=2^(a r)*P) (hp : parentEq b q w) :
    4*((w+1)*(w+1))<13*(r+1)*a r := by
  have hAP := feeder_AP_lt r P hP
  have hphys := physical_m_bound r b q w (by omega) hp
  have hPint : ((2:Int)^(a r)+3)*(P:Int)+(N r:Int)=((2:Int)^(a r))^(2*r) := by exact_mod_cast hP
  have hs := source_sparse r (P:Int) 1 hPint
  have hd := parent_int_dvd b q w hp
  have hbInt : 2*(b:Int)=(2:Int)^(a r)*(P:Int) := by exact_mod_cast hb
  apply first_narrow_cutoff r (w+1) hr (by omega) hphys
  simp only [value,Int.pow_zero,Int.mul_one,hs,Int.one_mul]
  have he : 5-2*((w+1:Nat):Int)+((2:Int)^(a r))*(P:Int)=2*(b:Int)+5-2*((w+1:Nat):Int) := by omega
  rwa [he]

/-- All members of the second-level progression, directly on the exact
    source parent equation, including its physical valuation range. -/
theorem second_source_equation_narrow_cutoff (j P b q w : Nat)
    (hP : (2^(a (110*j+50))+3)*P+N (110*j+50)=(2^(a (110*j+50)))^(2*(110*j+50)))
    (hb : 55*b=8*2^(a (110*j+50))*P+25) (hp : parentEq b q w) :
    4*((w+1)*(w+1))<13*((110*j+50)+1)*a (110*j+50) := by
  let r:=110*j+50
  have hAP := feeder_AP_lt r P hP
  have hbig : 1≤2^(2*r*a r) := Nat.two_pow_pos _
  have hb' : b<2^(2*r*a r) := by
    change 55*b=8*2^(a r)*P+25 at hb
    rw [Nat.mul_assoc] at hb
    omega
  have hphys := physical_m_bound r b q w hb' hp
  have hPint : ((2:Int)^(a r)+3)*(P:Int)+(N r:Int)=((2:Int)^(a r))^(2*r) := by exact_mod_cast hP
  have hs := source_sparse r (P:Int) 16 hPint
  have hd := parent_int_dvd b q w hp
  have hD : denominator (w+1)∣55*(2*(b:Int)+5-2*((w+1:Nat):Int)) := Int.dvd_mul_of_dvd_right hd
  have hbInt : 55*(b:Int)=8*(2:Int)^(a r)*(P:Int)+25 := by exact_mod_cast hb
  apply second_narrow_cutoff j (w+1) (by omega) hphys
  change denominator (w+1)∣value ((325-110*((w+1:Nat):Int),0)::sparse (a r) 16 (2*r))
  simp only [value,Int.pow_zero,Int.mul_one,hs]
  have he : 325-110*((w+1:Nat):Int)+16*(2:Int)^(a r)*(P:Int)=55*(2*(b:Int)+5-2*((w+1:Nat):Int)) := by
    rw [Int.mul_assoc 16,Int.mul_assoc 8] at *
    omega
  rwa [he]


#print axioms first_source_equation_narrow_cutoff
#print axioms second_source_equation_narrow_cutoff
end NeedleRotation.Cancellation
