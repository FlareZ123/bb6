import SourceBridge48
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
namespace A4Backward48

private theorem pow_mod24_all (m : Nat) (hm : 2≤m) :
    (2^(2*m+2))%24=16 := by
  have h : ∀ t:Nat, (2^(2*(t+2)+2))%24=16 := by
    intro t
    induction t with
    | zero => decide
    | succ t ih =>
        have he : 2*(t+1+2)+2=(2*(t+2)+2)+2 := by omega
        rw [he, Nat.pow_add]
        simp only [show (2:Nat)^2=4 by decide]
        omega
  have hh := h (m-2)
  have he : m-2+2=m := by omega
  simpa only [he] using hh

private theorem high_halt_mod24 (j m k : Nat)
    (hm : 2≤m)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (k+j+3*m+5)%24=(16*(j+3))%24 := by
  rw [heq]
  have hp:=pow_mod24_all m hm
  calc
    (2^(2*m+2)*(j+3))%24 = ((j+3)*(2^(2*m+2)))%24 := by rw [Nat.mul_comm]
    _ = ((j+3)*((2^(2*m+2))%24))%24 :=
      (Nat.mul_mod_mod (j+3) (2^(2*m+2)) 24).symm
    _ = ((j+3)*16)%24 := by rw [hp]
    _ = (16*(j+3))%24 := by rw [Nat.mul_comm]

/-- New source-connected uniform entire 3-adic/dyadic sector exclusion.
Every j divisible by four and m congruent four modulo eight is impossible
for the genuine blank-origin high-family stopping gateway, at all times. -/
theorem second_stop_j4_m8_4_excluded
    (j m k : Nat)
    (hj : j%4=0) (hm : m%8=4)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6CLine.Reach (2*j+3,k,0) := by
  intro hr
  have hm2 : 2≤m := by omega
  have hmod := high_halt_mod24 j m k hm2 heq
  have hcase : j%8=0 ∨ j%8=4 := by omega
  rcases hcase with h0 | h4
  · have ha : (2*j+3)%16=3 := by omega
    have hk : k%24=7 := by omega
    exact source_no_low48 (2*j+3) k (Or.inl ⟨ha,hk⟩) hr
  · have ha : (2*j+3)%16=11 := by omega
    have hk : k%24=19 := by omega
    exact source_no_low48 (2*j+3) k (Or.inr ⟨ha,hk⟩) hr

#print axioms second_stop_j4_m8_4_excluded
end A4Backward48
