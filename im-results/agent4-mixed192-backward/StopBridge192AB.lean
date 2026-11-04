import SourceBridge192Companion
import SourceBridge192B
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0
namespace A4Mixed192Stops

private theorem pow4_mod3 (m : Nat) : 4^m % 3 = 1 := by
  induction m with
  | zero => decide
  | succ m ih =>
      rw [Nat.pow_succ]
      omega

private theorem high_pow_mod192 (m : Nat) (hm : 2≤m) :
    2^(2*m+2)%192 = 64 := by
  have hp : 2^(2*m+2)=64*4^(m-2) := by
    have he : 2*m+2=6+2*(m-2) := by omega
    rw [he,Nat.pow_add]
    have ha : 2^(2*(m-2))=4^(m-2) := by
      calc
        2^(2*(m-2))=(2^2)^(m-2) := Nat.pow_mul 2 2 (m-2)
        _=4^(m-2) := by simp
    rw [ha]
  rw [hp]
  have ht := pow4_mod3 (m-2)
  omega

private theorem high_halt_mod192 (j m k : Nat)
    (hm : 2≤m)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    (k+j+3*m+5)%192 = (64*(j+3))%192 := by
  rw [heq]
  have hp := high_pow_mod192 m hm
  calc
    (2^(2*m+2)*(j+3))%192 = ((j+3)*(2^(2*m+2)))%192 := by rw [Nat.mul_comm]
    _ = ((j+3)*((2^(2*m+2))%192))%192 :=
        (Nat.mul_mod_mod (j+3) (2^(2*m+2)) 192).symm
    _ = ((j+3)*64)%192 := by rw [hp]
    _ = (64*(j+3))%192 := by rw [Nat.mul_comm]

/-- Genuine immediate high-stopping gates excluded by core A, for every allowed parameter. -/
theorem first_core_stops (j m k : Nat)
    (hm : 2≤m)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hres : (j%192=16 ∧ m%64=58) ∨
      (j%192=112 ∧ m%64=26) ∨
      (j%192=64 ∧ m%64=10) ∨
      (j%192=160 ∧ m%64=42)) :
    ¬ BB6CLine.Reach (2*j+3,k,0) := by
  intro hr
  have hmod := high_halt_mod192 j m k hm heq
  rcases hres with h | h | h | h
  · have ha : (2*j+3)%192=35 := by omega
    have hk : k%192=61 := by omega
    exact A4Backward192.source_no_35_61 (2*j+3) k ha hk hr
  · have ha : (2*j+3)%192=35 := by omega
    have hk : k%192=61 := by omega
    exact A4Backward192.source_no_35_61 (2*j+3) k ha hk hr
  · have ha : (2*j+3)%192=131 := by omega
    have hk : k%192=157 := by omega
    exact A4Backward192.source_no_131_157 (2*j+3) k ha hk hr
  · have ha : (2*j+3)%192=131 := by omega
    have hk : k%192=157 := by omega
    exact A4Backward192.source_no_131_157 (2*j+3) k ha hk hr

#print axioms first_core_stops

/-- Genuine immediate high-stopping gates excluded by core B, for every allowed parameter. -/
theorem second_core_stops (j m k : Nat)
    (hm : 2≤m)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hres : (j%192=40 ∧ m%64=2) ∨
      (j%192=136 ∧ m%64=34) ∨
      (j%192=88 ∧ m%64=18) ∨
      (j%192=184 ∧ m%64=50)) :
    ¬ BB6CLine.Reach (2*j+3,k,0) := by
  intro hr
  have hmod := high_halt_mod192 j m k hm heq
  rcases hres with h | h | h | h
  · have ha : (2*j+3)%192=83 := by omega
    have hk : k%192=13 := by omega
    exact A4Backward192B.source_no_83_13 (2*j+3) k ha hk hr
  · have ha : (2*j+3)%192=83 := by omega
    have hk : k%192=13 := by omega
    exact A4Backward192B.source_no_83_13 (2*j+3) k ha hk hr
  · have ha : (2*j+3)%192=179 := by omega
    have hk : k%192=109 := by omega
    exact A4Backward192B.source_no_179_109 (2*j+3) k ha hk hr
  · have ha : (2*j+3)%192=179 := by omega
    have hk : k%192=109 := by omega
    exact A4Backward192B.source_no_179_109 (2*j+3) k ha hk hr

#print axioms second_core_stops

end A4Mixed192Stops
