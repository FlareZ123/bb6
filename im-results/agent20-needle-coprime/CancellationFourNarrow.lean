import CancellationWide
import CancellationNarrowSource
import FourResidue

namespace NeedleRotation.Cancellation

/-- Uniform cutoff on any incoming edge into the prepared valuation-four parent. -/
theorem four_narrow_cutoff (r m : Nat) (hr : 8≤r) (hres : r%3=1)
    (hm : 0<m) (hmphys : m≤2*r*a r)
    (hd : denominator m∣value ((15-70*(m:Int),0)::sparse (a r) 32 (2*r))) :
    4*(m*m)<13*(r+1)*a r := by
  let C : Int := 15-70*(m:Int)
  have hC : C.natAbs≤110*m+325 := by dsimp [C]; omega
  have hCne : C≠0 := by dsimp [C]; omega
  have hMne : C-(2:Int)^5*(N r:Int)≠0 := by
    have hn := N_pos r
    dsimp [C]
    omega
  have hold : m*m<16*r*a r := by
    by_cases hma : m≤a r
    · by_cases hsmall : m*m<16*r*a r
      · exact hsmall
      exfalso
      have hD := CancellationWide.low_large_dvd r m 32 C hr hm hma (by omega) (by decide) hC hCne hd
      have hN := N_dvd_of_large r m C hm hma hD
      exact FourResidue.four_no_N_dvd r (a r) m hr hres (a_spec r) hm hma (by simpa [N,C] using hN)
    · exact False.elim (CancellationWide.high_no_dvd r m 5 C hr (by omega) hmphys (by decide) hC hCne hMne (by simpa [C] using hd))
  exact Asymmetric.narrow_cutoff r (N r) (a r) m 32 C hr
    (a_growth r hr) (a_spec r) (N_ge_81 r (by omega)) (N_lt_pow r (by omega))
    hm hold (by decide) hC hCne (sparse_to_three r m 32 C hd)

/-- Physical parent equation for a valuation-four ancestor: 70*b=32*AP-160. -/
theorem four_source_equation_narrow_cutoff (r P b q w : Nat) (hr : 8≤r) (hres : r%3=1)
    (hP : (2^(a r)+3)*P+N r=(2^(a r))^(2*r))
    (hb : 70*b+160=32*2^(a r)*P) (hp : parentEq b q w) :
    4*((w+1)*(w+1))<13*(r+1)*a r := by
  have hAP := feeder_AP_lt r P hP
  have hb' : b<2^(2*r*a r) := by
    rw [Nat.mul_assoc] at hb
    omega
  have hphys := physical_m_bound r b q w hb' hp
  have hPint : ((2:Int)^(a r)+3)*(P:Int)+(N r:Int)=((2:Int)^(a r))^(2*r) := by exact_mod_cast hP
  have hs := source_sparse r (P:Int) 32 hPint
  have hd := parent_int_dvd b q w hp
  have hD : denominator (w+1)∣35*(2*(b:Int)+5-2*((w+1:Nat):Int)) := Int.dvd_mul_of_dvd_right hd
  have hbInt : 70*(b:Int)+160=32*(2:Int)^(a r)*(P:Int) := by exact_mod_cast hb
  apply four_narrow_cutoff r (w+1) hr hres (by omega) hphys
  simp only [value,Int.pow_zero,Int.mul_one,hs]
  have he : 15-70*((w+1:Nat):Int)+32*(2:Int)^(a r)*(P:Int)=35*(2*(b:Int)+5-2*((w+1:Nat):Int)) := by
    rw [Int.mul_assoc 32] at *
    omega
  rwa [he]

#print axioms four_source_equation_narrow_cutoff
end NeedleRotation.Cancellation
