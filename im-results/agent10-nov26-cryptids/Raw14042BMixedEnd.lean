import Raw14042BMixedEndLocal
namespace Raw14042BMixedEnd
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double Raw14042Counter Raw14042BMixed Raw14042BMixedLocal Raw14042BMixedEndLocal
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
attribute [local irreducible] boundary run

theorem emptyEven (a b : Nat) (Y : List Sym) :
    Reach base (boundary 4 true [S 1] (U 1 a ++ S 5::S 2::S 2::(U 2 b ++ Y)))
      (boundary 1 true [S 5] (S 2::S 2::(U 1 (a+1) ++ S 2::S 3::(U 2 b ++ Y)))) := by
  let Z := U 3 a
  let V := U 2 b ++ Y
  have h0 := Raw140ERSweep.many a [] (S 5::S 2::S 2::V)
  have h1 := stepR base 4 4 true (S 5) (S 1) 7 (S 1::Z) (S 2::S 2::V) (by rfl)
  have h2 := Raw14042BMixedLocal.h1 Z V
  have h3 := sweepL base 4 (S 3) (S 1) 3 (a+1) [] (S 1::S 2::S 3::V) (by rfl)
  have h4 := end0 (U 1 (a+1) ++ S 2::S 3::V)
  have h01 := join h0 (by simpa only [List.append_nil,Z] using h1)
  have h02 := join h01 h2
  have h03 := join h02 (by simpa only [Z,U,List.replicate_succ,List.cons_append,List.append_nil] using h3)
  have h04 := join h03 (by simpa only [U,List.replicate_succ,List.cons_append,rep_cons] using h4)
  exact ⟨_,by simpa only [V,U,List.replicate_succ,List.cons_append,rep_cons,ite_true] using h04⟩
#print axioms emptyEven
end Raw14042BMixedEnd
