import PurePowerStop
import PurePowerFan
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 1000000

namespace BB6.Agent12PureFan
open BB6.Agent12PurePower

private theorem stop_linear_bound (m : Nat) (hm : 1≤m) : 3*m+5≤2^(2*m+1) := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases h : m=0
    · subst m; decide
    · have hh := ih (by omega)
      rw [show 2*(m+1)+1=2*m+1+2 by omega,Nat.pow_add]
      change 3*(m+1)+5≤2^(2*m+1)*4
      omega

/-- The pure-power stopping parametrization gives a large-height parent
    region and exact divisibility of j+3, not merely the parity of j. -/
theorem high_pure_data (j m y v : Nat) (hm : 1≤m)
    (hs : y+j+3*m+5=2^(2*m+2)*(j+3))
    (hq : 2*j+3+y+(2*j+3+y)%2=2^v) :
    let r := v%(2*m+2)
    3≤r ∧ r+(2*m+2)≤v ∧ 2^r∣j+3 ∧ 6*2^r≤y ∧
      v%2=1-(2*j+3+y)%2 ∧ 2^(v-1)≤y ∧
      2^r≤j+3 ∧ 2^(r+(2*m+2))∣j+3-2^r := by
  obtain ⟨r,s,hr,hc,ho,hv,hprod⟩ := high_power_exponent_form j m y v hm hs hq
  let b := 2*m+2
  let P := 2^b
  change v=b*(2*s+1)+r at hv
  change (P+1)*(j+3)=2^v+2^r at hprod
  change y+j+3*m+5=P*(j+3) at hs
  have hP16 : 16≤P := by
    change 2^4≤2^b
    exact Nat.pow_le_pow_right (by decide) (by dsimp [b]; omega)
  have hvr : r+b≤v := by
    have h := Nat.mul_le_mul_left b (show 1≤2*s+1 by omega)
    rw [Nat.mul_one] at h
    omega
  have hvr4 : r+4≤v := by dsimp [b] at hvr; omega
  have hP2 : P%2=0 := Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (show 1≤b by dsimp [b]; omega))
  have hpar := Nat.mul_mod P (j+3) 2
  rw [hP2,Nat.zero_mul,Nat.zero_mod] at hpar
  have hb2 : b%2=0 := by dsimp [b]; omega
  have hvpar : v%2=r%2 := by
    have h := Nat.mul_mod b (2*s+1) 2
    rw [hb2,Nat.zero_mul,Nat.zero_mod] at h
    omega
  have hp : P*2^r≤2^v := by
    rw [show P*2^r=2^(b+r) by exact (Nat.pow_add 2 b r).symm]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hJ : 2^r≤j+3 := by
    apply Nat.le_of_mul_le_mul_left (c:=P+1) _ (by omega)
    rw [hprod,Nat.add_mul,Nat.one_mul]
    omega
  have hh := high_stop_pure_power j m y v hm (by exact hs) hq
  have hre : v%b=r := by
    have hh' : 2^(v%b)+(j+m)%2=3*m+5 := hh.2.1
    have he : 2^(v%b)=2^r := by omega
    have h1 := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (Nat.le_of_eq he)
    have h2 := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (Nat.le_of_eq he.symm)
    omega
  have hrb : r<b := hre ▸ (Nat.mod_lt _ (by dsimp [b]; omega))
  have hPd : 2^r∣P := Nat.pow_dvd_pow 2 (by omega)
  have hPprod : 2^r∣P*(j+3) := Nat.dvd_trans hPd (Nat.dvd_mul_right _ _)
  have hQd : 2^r∣2^v := Nat.pow_dvd_pow 2 (by omega)
  have hsum : 2^r∣2^v+2^r := Nat.dvd_add hQd (Nat.dvd_refl _)
  rw [←hprod,Nat.add_mul,Nat.one_mul] at hsum
  have hjdiv : 2^r∣j+3 := (Nat.dvd_add_iff_right hPprod).mpr hsum
  have hlin := stop_linear_bound m hm
  have hPsplit : P=2^(2*m+1)*2 := by dsimp [P,b]; rw [show 2*m+2=2*m+1+1 by omega,Nat.pow_succ]
  have hmul := Nat.mul_le_mul_right (j+3) hP16
  have hmul2 : P≤P*(j+3) := Nat.le_mul_of_pos_right _ (by omega)
  have hmul3 : 8*(j+3)+P≤P*(j+3) := by
    have hh : P*(j+3)=P*(j+2)+P := by rw [show j+3=j+2+1 by omega,Nat.mul_add,Nat.mul_one]
    have h2 := Nat.mul_le_mul_right (j+2) hP16
    omega
  have hhalf : 2^(v-1)≤y := by
    have he : 2^v=2^(v-1)*2 := by
      calc
        2^v=2^(v-1+1) := by congr 1; omega
        _=2^(v-1)*2 := Nat.pow_succ 2 (v-1)
    omega
  have hPr : 2^(r+b)∣P*(j+3) := by
    rw [Nat.pow_add,Nat.mul_comm (2^r)]
    exact Nat.mul_dvd_mul (Nat.dvd_refl P) hjdiv
  have hQPr : 2^(r+b)∣2^v := Nat.pow_dvd_pow 2 (by omega)
  have hdiff : (j+3-2^r)+P*(j+3)=2^v := by
    rw [Nat.add_mul,Nat.one_mul] at hprod
    omega
  have hdvd : 2^(r+b)∣j+3-2^r := (Nat.dvd_add_iff_left hPr).mpr (hdiff ▸ hQPr)
  change 3≤v%b ∧ v%b+b≤v ∧ 2^(v%b)∣j+3 ∧ 6*2^(v%b)≤y ∧ _ ∧ 2^(v-1)≤y ∧ 2^(v%b)≤j+3 ∧ 2^(v%b+b)∣j+3-2^(v%b)
  rw [hre]
  exact ⟨hr,hvr,hjdiv,by omega,by omega,hhalf,hJ,hdvd⟩

theorem high_zero_pure_data (j y v : Nat)
    (hs : y+j+5=4*(j+3))
    (hq : 2*j+3+y+(2*j+3+y)%2=2^v) :
    8≤y ∧ v%2=1-(2*j+3+y)%2 := by
  obtain ⟨hv,hv4,hprod⟩ := (high_zero_power_iff j y v hs).mp hq
  have hq2 : 2^v%2=0 := Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (show 1≤v by omega))
  have hq16 : 16≤2^v := Nat.pow_le_pow_right (by decide : 0<2) hv
  omega

#print axioms high_pure_data
#print axioms high_zero_pure_data
end BB6.Agent12PureFan
