import P1Class

namespace BB6.Agent33Q1Class
open BB6.Agent4Cone
open BB6.Agent45TwoRoot

private theorem pow_lower (w : Nat) : w+1≤2^w := by
  induction w with
  | zero => decide
  | succ w ih =>
    rw [Nat.pow_succ]
    omega

private theorem shifted_power_lower (w : Nat) : w+1 ≤ 2^(32768*w) := by
  have hb := pow_lower w
  have he := Nat.pow_le_pow_right (show 0<(2:Nat) by decide)
    (show w ≤ 32768*w by omega)
  omega

private theorem main_power (w : Nat) :
    2^(16*(2048*w+1)) = 65536*2^(32768*w) := by
  have he : 16*(2048*w+1)=32768*w+16 := by omega
  rw [he, Nat.pow_add]
  rw [show (2:Nat)^16=65536 by decide]
  omega

theorem blank_no_critical_18_mod32768 (w : Nat) :
    ¬BB6.Agent1.Reach 2 (14*2^(32768*w+18)-2*(32768*w+18)-10) := by
  intro hr
  let S := 2^(32768*w)
  have hS : w+1 ≤ S := shifted_power_lower w
  have hP : 2^(16*(2048*w+1))=65536*S := main_power w
  have hU : u2 (2048*w+1)+8192*w+7=458752*S := by
    dsimp [u2]
    rw [hP]
    omega
  have h0b : 4*u2 (2048*w+1)-4=1835008*S-32768*w-32 := by omega
  have h0d : 4*u2 (2048*w+1)+9=1835008*S-32768*w-19 := by omega
  have h1b : 6*u2 (2048*w+1)-2=2752512*S-49152*w-44 := by omega
  have h1d : 2*u2 (2048*w+1)+5=917504*S-16384*w-9 := by omega
  have hh : BB6.Agent1.Reach 2
      (14*2^(16*(2048*w+1)+2)-2*(16*(2048*w+1)+2)-10) := by
    have he : 16*(2048*w+1)+2=32768*w+18 := by omega
    simpa only [he] using hr
  rcases (two_sector_critical_iff_feeders (2048*w+1) (by omega)).mp hh with h0 | h1
  · rw [h0b,h0d] at h0
    exact (blocked_no_reach _ _ (root0_blocked S w hS hP)) h0
  · rw [h1b,h1d] at h1
    exact (blocked_no_reach _ _ (root1_blocked S w hS hP)) h1

#print axioms blank_no_critical_18_mod32768
end BB6.Agent33Q1Class
