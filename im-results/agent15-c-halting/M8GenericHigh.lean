import M8OddTowerStructure
import Lean.Elab.Tactic.Omega
namespace BB6.Agent15Research
open BB6.Agent29Depth

/-- A complete Diophantine entry condition for the all-depth M8 forbidden
    cylinder, independent of a particular explicit stopping family. -/
theorem high_m8_diophantine_exclusion
    (m d t j : Nat)
    (hm : m%2=1)
    (hd : 1≤d)
    (hdpar : 2*d%4=(m+1)%4)
    (heq : allOddQ m*(j+3)=m+2^d*(2+8*t)) :
    ¬ BB6.Agent15.CReach (2*j+3) (3*2^d*(2+8*t)-2) := by
  have hQ4 : allOddQ m%4=1 := by
    simpa [allOddQ] using m8Geom4_mod_four (m+1) (by omega)
  obtain ⟨e,he⟩ : ∃e,d=e+1 := ⟨d-1,by omega⟩
  have hpow : 2^d=2*2^e := by
    rw [he,Nat.pow_succ]
    ac_rfl
  have hv : 2+8*t=2*(1+4*t) := by omega
  have hdiv4 : 4∣2^d*(2+8*t) := by
    refine ⟨2^e*(1+4*t),?_⟩
    rw [hpow,hv,show (4:Nat)=2*2 by decide]
    ac_rfl
  have hmod4 : (2^d*(2+8*t))%4=0 :=
    Nat.mod_eq_zero_of_dvd hdiv4
  have hjm : (j+3)%4=m%4 := by
    have hh := congrArg (fun z : Nat => z%4) heq
    rw [Nat.mul_mod,hQ4] at hh
    simp only [Nat.one_mul,Nat.mod_mod,Nat.add_mod,hmod4] at hh
    omega
  have hj2 : j%2=0 := by omega
  have hsum : (j+m)%4=3 := by omega
  have hpowerpos : 1≤2^d := Nat.pow_pos (by decide)
  have hvalpos : 2≤2+8*t := by omega
  have hmul : 2≤(2+8*t)*2^d := Nat.mul_le_mul hvalpos hpowerpos
  have hmul3 : 6≤3*2^d*(2+8*t) := by
    have hp := Nat.mul_le_mul_left 3 hmul
    have hcomm : 3*((2+8*t)*2^d)=3*2^d*(2+8*t) := by ac_rfl
    rw [hcomm] at hp
    omega
  have hk : (3*2^d*(2+8*t)-2)+2=3*2^d*(2+8*t) := by omega
  have hB := allOdd_BQ m
  have hmult : 3*allOddQ m*(j+3)=3*m+3*2^d*(2+8*t) := by
    calc
      3*allOddQ m*(j+3)=3*(allOddQ m*(j+3)) := by ac_rfl
      _=3*(m+2^d*(2+8*t)) := by rw [heq]
      _=3*m+3*2^d*(2+8*t) := by rw [Nat.mul_add]; ac_rfl
  have hstop : (3*2^d*(2+8*t)-2)+j+3*m+5=
      2^(2*m+2)*(j+3) := by
    have hB' : allOddB m*(j+3)=
        3*allOddQ m*(j+3)+(j+3) := by
      rw [hB]
      simp only [Nat.add_mul,Nat.one_mul]
    dsimp [allOddB] at hB'
    omega
  have hscale : (3*2^d*(2+8*t)-2)+2=3*(2+8*t)*2^d := by
    rw [hk]
    ac_rfl
  have hv8 : (2+8*t)%8=2 := by omega
  exact deep_no_root_of_data j m (3*2^d*(2+8*t)-2) d (2+8*t)
    hm hj2 hsum hstop hscale hv8 hdpar

#print axioms high_m8_diophantine_exclusion
end BB6.Agent15Research

