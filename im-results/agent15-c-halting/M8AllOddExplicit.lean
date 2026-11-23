import M8UniversalAlgebra
import Lean.Elab.Tactic.Omega
namespace BB6.Agent15Research
open BB6.Agent29Depth

/-- Geometric and affine quantities for an explicit all-odd M8 family. -/
def allOddB (m : Nat) : Nat := 2^(2*m+2)
def allOddQ (m : Nat) : Nat := m8Geom4 (m+1)
def allOddU (m d : Nat) : Nat := m+2^(d+1)
def allOddH (m d : Nat) : Nat := 2^(2*m+2-(d+3))
def allOddN (m d t : Nat) : Nat :=
  (allOddQ m-1)*allOddU m d+allOddQ m*(t+1)
def allOddV (m d t : Nat) : Nat := 2+8*allOddH m d*allOddN m d t
def allOddJ (m d t : Nat) : Nat :=
  (allOddB m-3)*(allOddU m d+1)+allOddB m*t
def allOddK (m d t : Nat) : Nat := 3*allOddV m d t*2^d-2

private theorem allOdd_pow_four (m : Nat) : allOddB m=4^(m+1) := by
  dsimp [allOddB]
  have hh : 2*m+2=2*(m+1) := by omega
  rw [hh,m8PowTwoDouble]

private theorem allOdd_BQ (m : Nat) : allOddB m=3*allOddQ m+1 := by
  rw [allOdd_pow_four]
  simpa [allOddQ] using (m8Geom4_three (m+1)).symm

private theorem allOdd_Qpos (m : Nat) : 1≤allOddQ m := by
  have hh : 1≤m+1 := by omega
  have hm := m8Geom4_mod_four (m+1) hh
  dsimp [allOddQ]
  omega

private theorem allOdd_Blower (m : Nat) (hm : 1≤m) : 16≤allOddB m := by
  have hb := allOdd_pow_four m
  obtain ⟨p,hp⟩ : ∃p, m+1=2+p := ⟨m-1,by omega⟩
  rw [hb,hp,Nat.pow_add]
  have hpos : 1≤4^p := Nat.pow_pos (by decide)
  omega

private theorem allOdd_Bfour (m : Nat) (_hm : 1≤m) : allOddB m%4=0 := by
  rw [allOdd_pow_four]
  have hp : m+1=1+m := by omega
  rw [hp,Nat.pow_add]
  simp

private theorem allOdd_pow_split (m d : Nat) (hd : d+3≤2*m+2) :
    allOddB m=8*2^d*allOddH m d := by
  let e := 2*m+2-(d+3)
  have he : d+3+e=2*m+2 := by dsimp [e]; omega
  change 2^(2*m+2)=8*2^d*2^e
  rw [← he,Nat.pow_add]
  have hthree : 2^(d+3)=8*2^d := by
    rw [show d+3=3+d by omega,Nat.pow_add]
  rw [hthree]

private theorem allOdd_Umod4 (m d : Nat) (hd : 1≤d) :
    (allOddU m d)%4=m%4 := by
  have hpow : 4∣2^(d+1) := by
    obtain ⟨r,hr⟩ : ∃r,d+1=2+r := ⟨d-1,by omega⟩
    refine ⟨2^r,?_⟩
    rw [hr,Nat.pow_add]
  have hh : 2^(d+1)%4=0 := Nat.mod_eq_zero_of_dvd hpow
  dsimp [allOddU]
  omega

private theorem allOdd_Jmod4 (m d t : Nat) (hm : 1≤m) (hd : 1≤d) :
    allOddJ m d t%4=(m+1)%4 := by
  have hB4 := allOdd_Bfour m hm
  have hB16 := allOdd_Blower m hm
  have hBsub : (allOddB m-3)%4=1 := by omega
  have hU : allOddU m d%4=m%4 := allOdd_Umod4 m d hd
  have hterm1 : ((allOddB m-3)*(allOddU m d+1))%4=
      (allOddU m d+1)%4 := by
    rw [Nat.mul_mod,hBsub]
    simp
  have hterm2 : (allOddB m*t)%4=0 := by
    rw [Nat.mul_mod,hB4]
    simp
  change ((allOddB m-3)*(allOddU m d+1)+allOddB m*t)%4=(m+1)%4
  rw [Nat.add_mod,hterm1,hterm2]
  omega

private theorem allOdd_V8 (m d t : Nat) : allOddV m d t%8=2 := by
  have hv : allOddV m d t=2+8*(allOddH m d*allOddN m d t) := by
    dsimp [allOddV]
    ac_rfl
  rw [hv]
  omega

private theorem allOdd_Kplus (m d t : Nat) :
    allOddK m d t+2=3*allOddV m d t*2^d := by
  have hV : 2≤allOddV m d t := by dsimp [allOddV]; omega
  have hpow : 1≤2^d := Nat.pow_pos (by decide)
  have hmult : 2≤allOddV m d t*2^d := Nat.mul_le_mul hV hpow
  have hmult3 : 6≤3*allOddV m d t*2^d := by
    have h := Nat.mul_le_mul_left 3 hmult
    simpa [Nat.mul_assoc] using h
  dsimp [allOddK]
  omega

private theorem allOdd_stop (m d t : Nat)
    (hm : 1≤m) (_hd : 1≤d) (hdmax : d+3≤2*m+2) :
    allOddK m d t+allOddJ m d t+3*m+5=
      2^(2*m+2)*(allOddJ m d t+3) := by
  have hB := allOdd_BQ m
  have hQ := allOdd_Qpos m
  have hH := allOdd_pow_split m d hdmax
  have hU : allOddU m d = m+2^(d+1) := rfl
  have hbound := allOdd_Blower m hm
  have hall := universal_algebra (allOddB m) (allOddQ m) (allOddH m d)
    (allOddU m d) m d t hB hQ hH hU (by omega)
  have hval : 3*allOddV m d t*2^d+allOddJ m d t+3*m+3=
      allOddB m*(allOddJ m d t+3) := by
    simpa [allOddJ,allOddN,allOddV] using hall
  have hK := allOdd_Kplus m d t
  dsimp [allOddB] at hval
  omega

/-- Every compatible odd m admits an infinite explicit family of genuine
    second-stopping inputs excluded from the authentic blank-origin orbit. -/
theorem allOdd_unreachable (m d t : Nat)
    (hm : m%2=1) (hd : 1≤d) (hdmax : d+3≤2*m+2)
    (hpar : 2*d%4=(m+1)%4) :
    ¬ BB6.Agent15.CReach (2*allOddJ m d t+3) (allOddK m d t) := by
  have hmpos : 1≤m := by omega
  have hj4 := allOdd_Jmod4 m d t hmpos hd
  have hj2 : allOddJ m d t%2=0 := by omega
  have hsum : (allOddJ m d t+m)%4=3 := by omega
  have hstop := allOdd_stop m d t hmpos hd hdmax
  have hv8 := allOdd_V8 m d t
  have hv4 : allOddV m d t%4=2 := by omega
  have hKplus := allOdd_Kplus m d t
  have hdepth : BB6.Agent15.oddDepth (allOddK m d t)=d := by
    have hh := m8OddDepth_scaled (allOddV m d t) d hv4
    rw [← hKplus] at hh
    simpa [allOddK] using hh
  have hdeep := BB6.Agent15.second_halt_deep_sector
    (allOddJ m d t) m (allOddK m d t) hstop hj2 hm hsum
  let p := BB6.Agent15.affineNormalize
    (2*allOddJ m d t+3) (allOddK m d t)
  have hscale : 2^d*(p.2+2)=allOddK m d t+2 := by
    simpa [p,hdepth] using hdeep.2.2.2.2
  have hv : p.2+2=3*allOddV m d t := by
    have hp : 0<2^d := Nat.pow_pos (by decide)
    have hh : 2^d*(p.2+2)=2^d*(3*allOddV m d t) := by
      calc
        2^d*(p.2+2)=allOddK m d t+2 := hscale
        _=3*allOddV m d t*2^d := hKplus
        _=2^d*(3*allOddV m d t) := by ac_rfl
    exact Nat.eq_of_mul_eq_mul_left hp hh
  have hquot : ((p.2+2)/3)%8=2 := by
    rw [hv]
    simpa using hv8
  intro hreach
  have hnot := second_deep_root_m8_parity_exclusion
    (allOddJ m d t) m (allOddK m d t) hstop hj2 hm hsum hreach
  exact hnot ⟨by simpa [p] using hquot, by rw [hdepth]; exact hpar⟩

/-- Depth one for m=1 mod 4 and depth two for m=3 mod 4. -/
def allOddDepth (m : Nat) : Nat := if m%4=1 then 1 else 2

/-- A single explicit infinite arithmetic progression of stopping inputs
    excluded for every positive odd m. -/
theorem allOdd_unreachable_every_odd (m t : Nat) (hm : m%2=1) :
    ¬ BB6.Agent15.CReach
      (2*allOddJ m (allOddDepth m) t+3) (allOddK m (allOddDepth m) t) := by
  by_cases hm1 : m%4=1
  · have hpar : 2*(1:Nat)%4=(m+1)%4 := by omega
    have hdmax : 1+3≤2*m+2 := by omega
    simpa [allOddDepth,hm1] using allOdd_unreachable m 1 t hm (by omega) hdmax hpar
  · have hm3 : m%4=3 := by omega
    have hpar : 2*(2:Nat)%4=(m+1)%4 := by omega
    have hdmax : 2+3≤2*m+2 := by omega
    have hd : allOddDepth m=2 := by simp [allOddDepth,hm1]
    simpa [hd] using allOdd_unreachable m 2 t hm (by omega) hdmax hpar

/-- The second-family index is an exact progression of step 2^(2m+2). -/
theorem allOdd_J_step (m d t : Nat) :
    allOddJ m d (t+1)=allOddJ m d t+allOddB m := by
  dsimp [allOddJ]
  simp only [Nat.mul_add, Nat.mul_one]
  ac_rfl

#print axioms allOdd_unreachable_every_odd
#print axioms allOdd_J_step
#print axioms allOdd_unreachable
end BB6.Agent15Research
