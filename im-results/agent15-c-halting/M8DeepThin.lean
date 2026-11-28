import M8ThinBridge
import SecondDeepSector
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6.Agent15Research

/-- M8-only copy of the exact affine-depth arithmetic, avoiding the combined
    M8/M16 certificate wrapper and its generated-namespace collision. -/
theorem m8OddDepth_scaled_thin (v d : Nat) (hv : v%4=2) :
    BB6.Agent15.oddDepth (3*v*2^d-2)=d := by
  induction d with
  | zero =>
      have hnot : ¬(4≤3*v-2 ∧ (3*v-2)%4=2) := by omega
      simp [BB6.Agent15.oddDepth, hnot]
  | succ d ih =>
      have hv2 : 2≤v := by omega
      have hpowPos : 1≤2^d := Nat.pow_pos (by decide : 0 < (2:Nat))
      have hpow2 : 2≤2^(d+1) := by
        rw [Nat.pow_succ]
        omega
      have hmul : 4≤v*2^(d+1) := Nat.mul_le_mul hv2 hpow2
      have hmul3 : 12≤3*v*2^(d+1) := by
        have h := Nat.mul_le_mul_left 3 hmul
        simpa [Nat.mul_assoc] using h
      have hkpos : 4≤3*v*2^(d+1)-2 := by omega
      have hvEven : v%2=0 := by omega
      have hfactor : 3*v*2^(d+1)=2*(3*v*2^d) := by
        rw [Nat.pow_succ]
        ac_rfl
      have hmul0 : 2≤v*2^d := Nat.mul_le_mul hv2 hpowPos
      have hmul0' : 6≤3*v*2^d := by
        have h := Nat.mul_le_mul_left 3 hmul0
        simpa [Nat.mul_assoc] using h
      have hzEven : (3*v*2^d)%2=0 := by
        simp [Nat.mul_mod, hvEven]
      have hkmod : (3*v*2^(d+1)-2)%4=2 := by
        rw [hfactor]
        omega
      have hstep : ((3*v*2^(d+1)-2)-2)/2=3*v*2^d-2 := by
        rw [hfactor]
        omega
      rw [BB6.Agent15.oddDepth, dif_pos ⟨hkpos,hkmod⟩, hstep, ih]
      omega

/-- Exact M8 deep-sector exclusion using only the M8 source certificate.
    This is logically the M8 half of the earlier combined quotient wrapper. -/
theorem deep_no_root_of_data_thin
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
    exact m8OddDepth_scaled_thin v d hv4
  have hdeep := BB6.Agent15.second_halt_deep_sector
    j m k hstop hj2 hm hs
  let p := BB6.Agent15.affineNormalize (2*j+3) k
  have hmass : p.1+2*p.2+4*d=2*j+3+2*k := by
    have h := hdeep.2.2.2.1
    simpa [p,hdepth] using h
  have hYscale : 2^d*(p.2+2)=k+2 := by
    have h := hdeep.2.2.2.2
    simpa [p,hdepth] using h
  have hY : p.2+2=3*v := by
    have hp : 0<2^d := Nat.pow_pos (by decide)
    have heq : 2^d*(p.2+2)=2^d*(3*v) := by
      calc
        2^d*(p.2+2)=k+2 := hYscale
        _=3*v*2^d := hscale
        _=2^d*(3*v) := by ac_rfl
    exact Nat.eq_of_mul_eq_mul_left hp heq
  have hy8 : p.2%8=4 := by omega
  have hkmod : k%4=2 := hdeep.2.1
  have hx8 : p.1%8=7 := by omega
  intro hreach
  have hnorm : BB6.Agent15.CReach p.1 p.2 := by
    simpa [p] using
      (BB6.Agent15.reach_iff_normalize (2*j+3) k).mp hreach
  have hx : p.1=8*(p.1/8)+7 := by omega
  have hy : p.2=8*(p.2/8)+4 := by omega
  rw [hx,hy] at hnorm
  exact BB6.Agent15.m8_blank_no_m8_cylinder (p.1/8) (p.2/8) hnorm

#print axioms m8OddDepth_scaled_thin
#print axioms deep_no_root_of_data_thin

end BB6.Agent15Research
