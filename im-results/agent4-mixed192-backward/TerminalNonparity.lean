import StopBridge192AB
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
namespace A4Mixed192Terminal

/-- An all-time genuine blank-root exclusion of an entire odd/odd
terminal plane cylinder, independent of any halting equation. -/
theorem source_no_side_41_31 (a k : Nat)
    (ha : a%48=41) (hk : k%48=31) (hbig : 4≤k)
    (hr : BB6CLine.Reach (a,k,0)) : False := by
  have hp := BB6.Agent46.reach_c0_two_parent a k hbig hr
  have h96 : a%96=41 ∨ a%96=89 := by omega
  rcases h96 with h41 | h89
  · have hh : A4Backward192B.high a (k-3) 3 := by
      simp only [A4Backward192B.high]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩)))))))
    have hn := A4Backward192B.source_blank_never_bad192B (a,k-3,3) hp
    apply hn
    simpa [A4Backward192B.bad] using hh
  · have hh : A4Backward192.high a (k-3) 3 := by
      simp only [A4Backward192.high]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega, by omega⟩))))))))))))))
    have hn := A4Backward192.source_blank_never_bad192 (a,k-3,3) hp
    apply hn
    simpa [A4Backward192.bad] using hh

/-- A second all-time genuine blank-root terminal exclusion, with a
non-Cartesian sum coupling modulo192 that cannot be lost. -/
theorem source_no_direct_35_13_96 (a k : Nat)
    (ha : a%48=35) (hk : k%48=13) (hs : (a+k)%192=96)
    (hr : BB6CLine.Reach (a,k,0)) : False := by
  have h192 : a%192=35 ∨ a%192=83 ∨
      a%192=131 ∨ a%192=179 := by omega
  rcases h192 with h35 | h83 | h131 | h179
  · exact A4Backward192.source_no_35_61 a k h35 (by omega) hr
  · exact A4Backward192B.source_no_83_13 a k h83 (by omega) hr
  · exact A4Backward192.source_no_131_157 a k h131 (by omega) hr
  · exact A4Backward192B.source_no_179_109 a k h179 (by omega) hr

#print axioms source_no_side_41_31
#print axioms source_no_direct_35_13_96
end A4Mixed192Terminal
