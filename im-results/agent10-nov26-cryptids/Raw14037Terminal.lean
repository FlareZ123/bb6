import Raw14037Counter
namespace Raw14037Terminal
open BB6BlockFAR Raw140Orbit Raw140Extra
open Raw140Double (Reach)
open Raw140ERSuffix Raw140ERSuffixLocal Raw140ERExit
open Raw14037SixBank (F inner turn1 turn5)
open Raw14037Counter (G)
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] boundary run

theorem onePrep (j v w : Nat) (X Y : List Sym) :
    Reach base
      (boundary 4 false (U 3 (j+1) ++ trip133 1 ++ S 2::S 2::(U 6 v ++ S 7::(U 3 (w+1) ++ X))) Y)
      (G (v+5) (U 3 w ++ X) (U 1 j ++ Y)) := by
  let Z := S 2::S 2::(U 6 v ++ S 7::(U 3 (w+1) ++ X))
  have h0 := prepareCarry j (S 3::S 3::Z) Y
  have h1 := stepR base 4 4 false (S 1) (S 5) 7 (S 3::S 3::S 3::Z) (U 1 j ++ Y) (by rfl)
  have h2 := sweepL base 4 (S 3) (S 1) 3 3 Z (S 5::(U 1 j ++ Y)) (by rfl)
  have h3 := inner v 3 (U 3 w ++ X) (U 1 j ++ Y)
  simp only [Z,trip133,U,List.replicate_succ,List.cons_append,List.replicate_zero,List.nil_append] at h0 h1 h2 h3
  have h := join (join (join h0 h1) h2) h3
  exact ⟨_, by simpa only [Z,G,trip133,U,List.replicate_succ,List.cons_append,List.replicate_zero,List.nil_append,List.append_assoc,show v+3+2=v+5 by omega] using h⟩

theorem one (v w : Nat) (s : Tail) (X : List Sym) :
    Reach base (F 1 v (w+1) s X)
      (G (v+5) (U 3 w ++ X) (trip115 (extra s) ++ tailWord (rho s))) := by
  let Z := trip133 1 ++ S 2::S 2::(U 6 v ++ S 7::(U 3 (w+1) ++ X))
  cases s with
  | t542 => exact Reach.trans ⟨_,prep542 Z⟩ (onePrep 1 v w X [S 5,S 2])
  | t152 => exact Reach.trans ⟨_,prep152 Z⟩ (onePrep 1 v w X [S 1,S 2,S 1])
  | t1121 => exact Reach.trans ⟨_,prep1121 Z⟩ (onePrep 0 v w X [S 5,S 2,S 1,S 5])
  | t5215 => exact Reach.trans ⟨_,prep5215 Z⟩ (onePrep 0 v w X [S 1,S 1,S 5,S 5])
  | t1155 => exact Reach.trans ⟨_,prep1155 Z⟩ (onePrep 2 v w X [S 5,S 1,S 1])
  | t11511 => exact Reach.trans ⟨_,prep11511 Z⟩ (onePrep 2 v w X [S 5,S 5,S 4,S 2])

#print axioms one
end Raw14037Terminal
