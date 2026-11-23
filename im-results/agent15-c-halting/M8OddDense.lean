import M8AllOddExplicit
import Lean.Elab.Tactic.Omega
namespace BB6.Agent15Research
open BB6.Agent29Depth

/-- Replace the sparse step 2^(2m+2) by the full M8 congruence step
    2^(d+3), retaining the exact second-family halting equation. -/
def allOddDenseJ (m d t : Nat) : Nat :=
  allOddJ m d 0+2^(d+3)*t
def allOddDenseV (m d t : Nat) : Nat :=
  allOddV m d 0+8*allOddQ m*t
def allOddDenseK (m d t : Nat) : Nat :=
  3*allOddDenseV m d t*2^d-2

private theorem allOddDense_pow (d : Nat) : 2^(d+3)=8*2^d := by
  rw [show d+3=3+d by omega, Nat.pow_add]

private theorem allOddDense_stop (m d t : Nat)
    (hm : 1≤m) (hd : 1≤d) (hdmax : d+3≤2*m+2) :
    allOddDenseK m d t+allOddDenseJ m d t+3*m+5=
      allOddB m*(allOddDenseJ m d t+3) := by
  let B := allOddB m
  let Q := allOddQ m
  let j0 := allOddJ m d 0
  let v0 := allOddV m d 0
  let P := 2^(d+3)
  let j := allOddDenseJ m d t
  let v := allOddDenseV m d t
  have hB : B=3*Q+1 := allOdd_BQ m
  have hP : P=8*2^d := allOddDense_pow d
  have hbaseStop := allOdd_stop m d 0 hm hd hdmax
  have hbaseK := allOdd_Kplus m d 0
  have hbase : 3*v0*2^d+j0+3*m+3=B*(j0+3) := by
    have hsrc : allOddK m d 0+allOddJ m d 0+3*m+5=
        allOddB m*(allOddJ m d 0+3) := by
      simpa [allOddB] using hbaseStop
    dsimp only [B,j0,v0]
    omega
  have hinc : 3*(8*Q*t)*2^d+P*t=B*(P*t) := by
    rw [hB,hP]
    simp only [Nat.add_mul,Nat.one_mul]
    ac_rfl
  have hval : 3*v*2^d+j+3*m+3=B*(j+3) := by
    calc
      3*v*2^d+j+3*m+3 =
        (3*v0*2^d+j0+3*m+3)+(3*(8*Q*t)*2^d+P*t) := by
          change 3*(v0+8*Q*t)*2^d+(j0+P*t)+3*m+3 =
            (3*v0*2^d+j0+3*m+3)+(3*(8*Q*t)*2^d+P*t)
          simp only [Nat.add_mul, Nat.mul_add]
          ac_rfl
      _ = B*(j0+3)+B*(P*t) := by rw [hbase,hinc]
      _ = B*(j+3) := by
          change B*(j0+3)+B*(P*t) = B*(j0+P*t+3)
          rw [show j0+P*t+3=(j0+3)+P*t by omega]
          simp only [Nat.mul_add]
  have hvpos : 2≤v := by dsimp [v,allOddDenseV,allOddV]; omega
  have hpow : 1≤2^d := Nat.pow_pos (by decide)
  have hmult : 2≤v*2^d := Nat.mul_le_mul hvpos hpow
  have hmult3 : 6≤3*v*2^d := by
    have hh := Nat.mul_le_mul_left 3 hmult
    simpa [Nat.mul_assoc] using hh
  have hk : allOddDenseK m d t+2=3*v*2^d := by
    change (3*v*2^d-2)+2=3*v*2^d
    omega
  change allOddDenseK m d t+j+3*m+5=B*(j+3)
  omega

private theorem allOddDense_Jmod4 (m d t : Nat)
    (hm : 1≤m) (hd : 1≤d) :
    allOddDenseJ m d t%4=(m+1)%4 := by
  have hj0 := allOdd_Jmod4 m d 0 hm hd
  have hp : 2^(d+3)=8*2^d := allOddDense_pow d
  have hs : (2^(d+3)*t)%4=0 := by
    rw [hp]
    have hh : 8*2^d*t=4*(2*(2^d*t)) := by
      rw [show (8:Nat)=4*2 by decide]
      ac_rfl
    rw [hh]
    omega
  dsimp [allOddDenseJ]
  omega

private theorem allOddDense_V8 (m d t : Nat) :
    allOddDenseV m d t%8=2 := by
  have hv0 := allOdd_V8 m d 0
  have ht : 8*allOddQ m*t=8*(allOddQ m*t) := by ac_rfl
  dsimp [allOddDenseV]
  rw [ht]
  omega

/-- Explicit dense index progression excluded by the source M8 cylinder,
    conditional on its separately source-checked imported theorems. -/
theorem allOddDense_unreachable (m d t : Nat)
    (hm : m%2=1) (hd : 1≤d) (hdmax : d+3≤2*m+2)
    (hpar : 2*d%4=(m+1)%4) :
    ¬ BB6.Agent15.CReach (2*allOddDenseJ m d t+3)
      (allOddDenseK m d t) := by
  have hmpos : 1≤m := by omega
  have hj4 := allOddDense_Jmod4 m d t hmpos hd
  have hj2 : allOddDenseJ m d t%2=0 := by omega
  have hsum : (allOddDenseJ m d t+m)%4=3 := by omega
  have hstop := allOddDense_stop m d t hmpos hd hdmax
  have hstop' : allOddDenseK m d t+allOddDenseJ m d t+3*m+5=
      2^(2*m+2)*(allOddDenseJ m d t+3) := by
    simpa [allOddB] using hstop
  have hv8 := allOddDense_V8 m d t
  have hv4 : allOddDenseV m d t%4=2 := by omega
  have hdepth : BB6.Agent15.oddDepth (allOddDenseK m d t)=d := by
    simpa [allOddDenseK] using m8OddDepth_scaled
      (allOddDenseV m d t) d hv4
  have hdeep := BB6.Agent15.second_halt_deep_sector
    (allOddDenseJ m d t) m (allOddDenseK m d t) hstop' hj2 hm hsum
  let p := BB6.Agent15.affineNormalize
    (2*allOddDenseJ m d t+3) (allOddDenseK m d t)
  have hscale : 2^d*(p.2+2)=allOddDenseK m d t+2 := by
    simpa [p,hdepth] using hdeep.2.2.2.2
  have hK : allOddDenseK m d t+2=3*allOddDenseV m d t*2^d := by
    have hvpos : 2≤allOddDenseV m d t := by
      dsimp [allOddDenseV,allOddV]
      omega
    have hpow : 1≤2^d := Nat.pow_pos (by decide)
    have hmult : 2≤allOddDenseV m d t*2^d :=
      Nat.mul_le_mul hvpos hpow
    have hmult3 : 6≤3*allOddDenseV m d t*2^d := by
      have h := Nat.mul_le_mul_left 3 hmult
      simpa [Nat.mul_assoc] using h
    dsimp [allOddDenseK]
    omega
  have hY : p.2+2=3*allOddDenseV m d t := by
    have hpos : 0<2^d := Nat.pow_pos (by decide)
    have heq : 2^d*(p.2+2)=2^d*(3*allOddDenseV m d t) := by
      calc
        2^d*(p.2+2)=allOddDenseK m d t+2 := hscale
        _=3*allOddDenseV m d t*2^d := hK
        _=2^d*(3*allOddDenseV m d t) := by ac_rfl
    exact Nat.eq_of_mul_eq_mul_left hpos heq
  have hquot : ((p.2+2)/3)%8=2 := by
    rw [hY]
    simpa using hv8
  intro hreach
  have hnot := second_deep_root_m8_parity_exclusion
    (allOddDenseJ m d t) m (allOddDenseK m d t)
    hstop' hj2 hm hsum hreach
  exact hnot ⟨by simpa [p] using hquot, by rw [hdepth]; exact hpar⟩

/-- For each odd m, one full 16- or 32-residue progression is excluded. -/
theorem allOddDense_every_odd (m t : Nat) (hm : m%2=1) :
    ¬ BB6.Agent15.CReach
      (2*allOddDenseJ m (allOddDepth m) t+3)
      (allOddDenseK m (allOddDepth m) t) := by
  by_cases h : m%4=1
  · have hmax : 1+3≤2*m+2 := by omega
    have hpar : 2*(1:Nat)%4=(m+1)%4 := by omega
    simpa [allOddDepth,h] using allOddDense_unreachable m 1 t hm (by omega) hmax hpar
  · have h3 : m%4=3 := by omega
    have hmax : 2+3≤2*m+2 := by omega
    have hpar : 2*(2:Nat)%4=(m+1)%4 := by omega
    simpa [allOddDepth,h] using allOddDense_unreachable m 2 t hm (by omega) hmax hpar

theorem allOddDense_J_step (m d t : Nat) :
    allOddDenseJ m d (t+1)=allOddDenseJ m d t+2^(d+3) := by
  dsimp [allOddDenseJ]
  simp only [Nat.mul_add,Nat.mul_one]
  ac_rfl

#print axioms allOddDense_every_odd
#print axioms allOddDense_J_step
end BB6.Agent15Research
