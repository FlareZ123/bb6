import Raw14042ExtraTailLocal
namespace Raw14042ExtraTail
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double Raw14042Bank Raw14042ExtraTailLocal
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
attribute [local irreducible] boundary run

theorem return11 (n p : Nat) :
    Reach Raw140VariantTransfer.M42
      (boundary 0 true (U 3 (p+1) ++ [S 2]) (T (n+2) ++ [S 1,S 1]))
      (boundary 0 true (U 3 (p+13) ++ [S 2]) (T n ++ [S 5,S 4,S 2])) := by
  have h₁ := Raw140VariantTransfer.transferMany42 (n+1) (U 3 (p+1) ++ [S 2]) [S 1,S 1]
  have ext : Extends Raw140VariantTransfer.M42 := by
    unfold Raw140VariantTransfer.M42
    exact fill_extends _ _
  have h₂ := prep11 (B (n+1) ++ ([S 2,S 5] ++ U 3 (p+1) ++ [S 2])) []
  have h₃ := start42 0 n p [S 5,S 4,S 2]
  have h₄ : Reach base
      (boundary 4 true (S 1::(B (n+1) ++ [S 2,S 5] ++ U 3 (p+1) ++ [S 2])) [S 1,S 1])
      (boundary 0 true (U 3 (p+13) ++ [S 2]) (T n ++ [S 5,S 4,S 2])) := by
    simp only [U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h₃
    exact Reach.trans ⟨_,by simpa only [U,List.replicate_succ,List.cons_append,List.append_assoc,List.nil_append] using h₂⟩ h₃
  have h₁' : Reach Raw140VariantTransfer.M42
      (boundary 0 true (U 3 (p+1) ++ [S 2]) (T (n+2) ++ [S 1,S 1]))
      (boundary 4 true (S 1::(B (n+1) ++ [S 2,S 5] ++ U 3 (p+1) ++ [S 2])) [S 1,S 1]) := by
    refine ⟨37+45*(n+1), ?_⟩
    simpa only [T,B,Raw140VariantTransfer.trip,List.cons_append,List.nil_append,List.append_assoc] using h₁
  exact Reach.trans h₁' (Reach.ext ext h₄)
#print axioms return11
end Raw14042ExtraTail
