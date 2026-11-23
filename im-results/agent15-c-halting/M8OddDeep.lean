import M8OddDeepAlgebra
import Lean.Elab.Tactic.Omega
namespace BB6.Agent15Research
open BB6.Agent29Depth

/-- For m>=1 the geometric quotient 1+4+...+4^m is 5 modulo 16. -/
theorem deepQ_mod16 (m : Nat) (hm : 1≤m) : allOddQ m%16=5 := by
  cases m with
  | zero => omega
  | succ n =>
      change (4*(4*m8Geom4 n+1)+1)%16=5
      omega

def deepTail (m t : Nat) : Nat :=
  if m%4=1 then 15+16*t else 5+8*t
def deepIndex (m t : Nat) : Nat :=
  (allOddB m-3)*(m+1)+allOddB m*deepTail m t
def deepMass (m t : Nat) : Nat :=
  (allOddQ m-1)*m+allOddQ m*(deepTail m t+1)
def deepDepth (m : Nat) : Nat :=
  if m%4=1 then 2*m+3 else 2*m+2
def deepV (m t : Nat) : Nat :=
  if m%4=1 then deepMass m t/2 else deepMass m t
def deepK (m t : Nat) : Nat := 3*allOddB m*deepMass m t-2

private theorem deepB_mod4 (m : Nat) : allOddB m%4=0 := by
  change 2^(2*m+2)%4=0
  rw [show 2*m+2=2+2*m by omega,Nat.pow_add]
  simp

private theorem deepJ_mod4 (m t : Nat) (hm : 1≤m) :
    deepIndex m t%4=(m+1)%4 := by
  have hB4 := deepB_mod4 m
  have hBQ := allOdd_BQ m
  have hQ16 := deepQ_mod16 m hm
  have hQpos : 1≤allOddQ m := by omega
  have hB3 : 3≤allOddB m := by omega
  have hBsub : (allOddB m-3)%4=1 := by omega
  have hmul : ((allOddB m-3)*(m+1))%4=(m+1)%4 := by
    rw [Nat.mul_mod,hBsub]
    simp
  have hmul2 : (allOddB m*deepTail m t)%4=0 := by
    rw [Nat.mul_mod,hB4]
    simp
  dsimp [deepIndex]
  rw [Nat.add_mod,hmul,hmul2]
  omega

private theorem deepN_mod16_one (m t : Nat)
    (hm : m%4=1) : deepMass m t%16=4 := by
  have hmpos : 1≤m := by omega
  have hQ16 := deepQ_mod16 m hmpos
  have hQsub : (allOddQ m-1)%16=4 := by omega
  have htail : (deepTail m t+1)%16=0 := by
    dsimp [deepTail]
    rw [if_pos hm]
    omega
  dsimp [deepMass]
  rw [Nat.add_mod]
  rw [Nat.mul_mod (allOddQ m-1) m 16]
  rw [Nat.mul_mod (allOddQ m) (deepTail m t+1) 16]
  rw [hQsub,hQ16,htail]
  omega

private theorem deepN_mod8_three (m t : Nat)
    (hm : m%4=3) : deepMass m t%8=2 := by
  have hmpos : 1≤m := by omega
  have hQ16 := deepQ_mod16 m hmpos
  have hQ8 : allOddQ m%8=5 := by omega
  have hQsub : (allOddQ m-1)%8=4 := by omega
  have htail : (deepTail m t+1)%8=6 := by
    dsimp [deepTail]
    have hnot : ¬m%4=1 := by omega
    rw [if_neg hnot]
    omega
  dsimp [deepMass]
  rw [Nat.add_mod]
  rw [Nat.mul_mod (allOddQ m-1) m 8]
  rw [Nat.mul_mod (allOddQ m) (deepTail m t+1) 8]
  rw [hQsub,hQ8,htail]
  omega

/-- Exact original second-family stopping equation for all odd m. -/
theorem deep_stop (m t : Nat) (hm : m%2=1) :
    deepK m t+deepIndex m t+3*m+5=
      allOddB m*(deepIndex m t+3) := by
  have hmpos : 1≤m := by omega
  have hQ16 := deepQ_mod16 m hmpos
  have hQ : 1≤allOddQ m := by omega
  have hB := allOdd_BQ m
  have hB3 : 3≤allOddB m := by omega
  have hall := deep_algebra (allOddB m) (allOddQ m) m
    (deepTail m t) hB hQ hB3
  have hval : 3*allOddB m*deepMass m t+deepIndex m t+3*m+3=
      allOddB m*(deepIndex m t+3) := by
    simpa [deepMass,deepIndex] using hall
  have hn : 2≤deepMass m t := by
    by_cases hm1 : m%4=1
    · have hh := deepN_mod16_one m t hm1
      omega
    · have hm3 : m%4=3 := by omega
      have hh := deepN_mod8_three m t hm3
      omega
  have hBn : 1≤allOddB m := by omega
  have hmul : 2≤allOddB m*deepMass m t := Nat.mul_le_mul hBn hn
  have hmul3 : 6≤3*allOddB m*deepMass m t := by
    have hh := Nat.mul_le_mul_left 3 hmul
    simpa [Nat.mul_assoc] using hh
  have hk : deepK m t+2=3*allOddB m*deepMass m t := by
    dsimp [deepK]
    omega
  omega

private theorem deep_no_root_of_data
    (j m k d v : Nat)
    (hm : m%2=1) (hj2 : j%2=0) (hs : (j+m)%4=3)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hscale : k+2=3*v*2^d)
    (hv8 : v%8=2)
    (hdpar : 2*d%4=(m+1)%4) :
    ¬ BB6.Agent15.CReach (2*j+3) k := by
  have hv4 : v%4=2 := by omega
  have hk : k=3*v*2^d-2 := by omega
  have hdepth : BB6.Agent15.oddDepth k=d := by
    rw [hk]
    exact m8OddDepth_scaled v d hv4
  have hdeep := BB6.Agent15.second_halt_deep_sector
    j m k hstop hj2 hm hs
  let p := BB6.Agent15.affineNormalize (2*j+3) k
  have hYscale : 2^d*(p.2+2)=k+2 := by
    simpa [p,hdepth] using hdeep.2.2.2.2
  have hY : p.2+2=3*v := by
    have hp : 0<2^d := Nat.pow_pos (by decide)
    have heq : 2^d*(p.2+2)=2^d*(3*v) := by
      calc
        2^d*(p.2+2)=k+2 := hYscale
        _=3*v*2^d := hscale
        _=2^d*(3*v) := by ac_rfl
    exact Nat.eq_of_mul_eq_mul_left hp heq
  have hquot : ((p.2+2)/3)%8=2 := by
    rw [hY]
    simpa using hv8
  intro hreach
  have hnot := second_deep_root_m8_parity_exclusion
    j m k hstop hj2 hm hs hreach
  exact hnot ⟨by simpa [p] using hquot,by rw [hdepth]; exact hdpar⟩

/-- For every odd m, exclude a deep-stopping progression at odd depth
    2m+2 (m=3 mod 4), or 2m+3 (m=1 mod 4). -/
theorem deep_every_odd_unreachable (m t : Nat) (hm : m%2=1) :
    ¬ BB6.Agent15.CReach (2*deepIndex m t+3) (deepK m t) := by
  have hmpos : 1≤m := by omega
  have hj4 := deepJ_mod4 m t hmpos
  have hj2 : deepIndex m t%2=0 := by omega
  have hs : (deepIndex m t+m)%4=3 := by omega
  have hstop := deep_stop m t hm
  have hstop' : deepK m t+deepIndex m t+3*m+5=
      2^(2*m+2)*(deepIndex m t+3) := by
    simpa [allOddB] using hstop
  have hn : 2≤deepMass m t := by
    by_cases hm1 : m%4=1
    · have hh := deepN_mod16_one m t hm1
      omega
    · have hm3 : m%4=3 := by omega
      have hh := deepN_mod8_three m t hm3
      omega
  have hBpos : 1≤allOddB m := by
    have hh := allOdd_BQ m
    omega
  have hmul : 2≤allOddB m*deepMass m t :=
    Nat.mul_le_mul hBpos hn
  have hmult3 : 6≤3*allOddB m*deepMass m t := by
    have hh := Nat.mul_le_mul_left 3 hmul
    simpa [Nat.mul_assoc] using hh
  have hk : deepK m t+2=3*allOddB m*deepMass m t := by
    dsimp [deepK]
    omega
  by_cases hm1 : m%4=1
  · have hn16 := deepN_mod16_one m t hm1
    have hv8 : (deepMass m t/2)%8=2 := by omega
    have hnHalf : 2*(deepMass m t/2)=deepMass m t := by omega
    have hpow : 2^(2*m+3)=2*allOddB m := by
      dsimp [allOddB]
      rw [show 2*m+3=(2*m+2)+1 by omega,Nat.pow_succ]
      ac_rfl
    have hscale : deepK m t+2=3*(deepMass m t/2)*2^(2*m+3) := by
      have hn2 : allOddB m*deepMass m t =
          allOddB m*(2*(deepMass m t/2)) :=
        congrArg (fun z => allOddB m*z) hnHalf.symm
      calc
        deepK m t+2=3*allOddB m*deepMass m t := hk
        _ = 3*allOddB m*(2*(deepMass m t/2)) := by
          calc
            3*allOddB m*deepMass m t=3*(allOddB m*deepMass m t) := by ac_rfl
            _ = 3*(allOddB m*(2*(deepMass m t/2))) := by rw [hn2]
            _ = 3*allOddB m*(2*(deepMass m t/2)) := by ac_rfl
        _ = 3*(deepMass m t/2)*(2*allOddB m) := by ac_rfl
        _ = 3*(deepMass m t/2)*2^(2*m+3) := by rw [hpow]
    have hpar : 2*(2*m+3)%4=(m+1)%4 := by omega
    exact deep_no_root_of_data (deepIndex m t) m (deepK m t)
      (2*m+3) (deepMass m t/2) hm hj2 hs hstop' hscale hv8 hpar
  · have hm3 : m%4=3 := by omega
    have hn8 := deepN_mod8_three m t hm3
    have hscale : deepK m t+2=3*deepMass m t*2^(2*m+2) := by
      rw [hk]
      dsimp [allOddB]
      ac_rfl
    have hpar : 2*(2*m+2)%4=(m+1)%4 := by omega
    exact deep_no_root_of_data (deepIndex m t) m (deepK m t)
      (2*m+2) (deepMass m t) hm hj2 hs hstop' hscale hn8 hpar

/-- Exact increment of the explicit high-depth progression in j. -/
theorem deepIndex_step (m t : Nat) :
    deepIndex m (t+1)=deepIndex m t+
      allOddB m*(if m%4=1 then 16 else 8) := by
  by_cases h : m%4=1
  · dsimp [deepIndex,deepTail]
    simp only [h,ite_true,Nat.mul_add,Nat.mul_one]
    ac_rfl
  · dsimp [deepIndex,deepTail]
    simp only [h,ite_false,Nat.mul_add,Nat.mul_one]
    ac_rfl

#print axioms deep_every_odd_unreachable
#print axioms deepIndex_step
end BB6.Agent15Research
