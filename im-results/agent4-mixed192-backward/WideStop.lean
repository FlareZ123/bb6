import StopBridge192AB
import Agent46TerminalLifts
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
namespace A4Mixed192Wide

theorem high_gate_cover (j m k : Nat)
    (hj : j%12=4) (hm : m%8=4)
    (hk : 4≤k)
    (hmod : (k+j+3*m+5)%192=(64*(j+3))%192) :
    A4Backward192.high (2*j+3) (k-3) 3 ∨
    A4Backward192B.high (2*j+3) (k-3) 3 := by
  have hj48 : j%48=4 ∨ j%48=16 ∨ j%48=28 ∨ j%48=40 := by omega
  have hm16 : m%16=4 ∨ m%16=12 := by omega
  rcases hj48 with h4 | h16 | h28 | h40
  · rcases hm16 with hm4 | hm12
    · right
      simp only [A4Backward192B.high]
      exact Or.inr (Or.inl (⟨by omega, by omega⟩))
    · left
      simp only [A4Backward192.high]
      exact Or.inr (Or.inl (⟨by omega, by omega⟩))
  · rcases hm16 with hm4 | hm12
    · right
      simp only [A4Backward192B.high]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))
    · left
      simp only [A4Backward192.high]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, Or.inl (by omega)⟩)))))
  · rcases hm16 with hm4 | hm12
    · right
      simp only [A4Backward192B.high]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))
    · left
      simp only [A4Backward192.high]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))
  · rcases hm16 with hm4 | hm12
    · right
      simp only [A4Backward192B.high]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, Or.inl (by omega)⟩))))))))))))))
    · left
      simp only [A4Backward192.high]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))))))))


theorem second_stop_j4_mod12_m4_mod8_excluded
    (j m k : Nat)
    (hj : j%12=4) (hm : m%8=4)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ¬ BB6CLine.Reach (2*j+3,k,0) := by
  intro hr
  have hm1 : 1≤m := by omega
  have hm2 : 2≤m := by omega
  have hpower : 3*m+9≤2^(2*m+2) := BB6.Agent46.pow_bound m hm1
  have hpositive : 1≤2^(2*m+2) := by omega
  have hjmul : j≤2^(2*m+2)*j := by
    simpa using Nat.mul_le_mul_right j hpositive
  have hprod : 2^(2*m+2)*(j+3) =
      2^(2*m+2)*j + 3*2^(2*m+2) := by
    simp [Nat.mul_add, Nat.mul_comm]
  have hk : 4≤k := by
    rw [hprod] at heq
    omega
  have hmod := A4Mixed192Stops.high_halt_mod192 j m k hm2 heq
  have hp : BB6CLine.Reach (2*j+3,k-3,3) :=
    BB6.Agent46.reach_c0_two_parent (2*j+3) k hk hr
  rcases high_gate_cover j m k hj hm hk hmod with ha | hb
  · have hn := A4Backward192.source_blank_never_bad192 (2*j+3,k-3,3) hp
    apply hn
    simpa [A4Backward192.bad] using ha
  · have hn := A4Backward192B.source_blank_never_bad192B (2*j+3,k-3,3) hp
    apply hn
    simpa [A4Backward192B.bad] using hb

#print axioms high_gate_cover
#print axioms second_stop_j4_mod12_m4_mod8_excluded
end A4Mixed192Wide
