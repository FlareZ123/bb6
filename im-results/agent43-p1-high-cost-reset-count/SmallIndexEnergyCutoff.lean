import Lean
import RootTwoDivisor
import Lean.Elab.Tactic.Omega

namespace BB6.Agent43FiniteBridge
open BB6.Agent43TwoRun

/-- Exact root two-run divisibility forces a tiny root prefix for 14<=n<48. -/
theorem root_two_prefix_le_three
    (n s : Nat) (Wa Ba : Int) (hn : 14≤n) (hn48 : n<48)
    (h : TwoRun ((2:Int)^n)
      (14*(2:Int)^n+2*(n:Int)+4) ((n:Int)+6) s Wa Ba) : s≤3 := by
  obtain ⟨_,hd⟩ := root_two_prefix_divisor n s Wa Ba hn h
  obtain ⟨d,heq⟩ := hd
  have hdpos : 0<d := by
    by_cases hd0 : d=0
    · rw [hd0] at heq
      simp at heq
    · omega
  have hle : 8^s ≤ 14*n+92 := by
    have hmul : 8^s≤8^s*d := by
      simpa using (Nat.mul_le_mul_left (8^s) hdpos)
    omega
  by_cases hs3 : s≤3
  · exact hs3
  have hs4 : 4≤s := by omega
  have hpow : (8:Nat)^4≤8^s := Nat.pow_le_pow_right (by decide) hs4
  have h4 : (8:Nat)^4=4096 := by decide
  rw [h4] at hpow
  omega

/-- A depth-two chain of length at least three forces a 512 factor in
its initial affine energy. No assumptions about its end coordinates. -/
theorem two_run_energy_div512
    (P Wa Ba Wb Bb : Int) (u : Nat)
    (hu : 3≤u) (h : TwoRun P Wa Ba u Wb Bb) :
    (512:Int) ∣ I P Wa Ba := by
  have henergy := run_energy P Wa Ba Wb Bb u h
  have he : u=3+(u-3) := by omega
  refine ⟨((8:Int)^(u-3))*I P Wb Bb, ?_⟩
  rw [henergy,he, Int.pow_add]
  have h8cube : (8:Int)^3=512 := by decide
  rw [h8cube]
  have he2 : 3+(u-3)-3=u-3 := by omega
  rw [he2]
  ac_rfl

#print axioms BB6.Agent43FiniteBridge.root_two_prefix_le_three
#print axioms BB6.Agent43FiniteBridge.two_run_energy_div512
end BB6.Agent43FiniteBridge