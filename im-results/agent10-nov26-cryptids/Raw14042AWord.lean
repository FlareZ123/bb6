import Raw14042AWordLocal
namespace Raw14042AWord
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double Raw14042AWordLocal
open Raw140ERSuffix (tailWord rho)
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
attribute [local irreducible] boundary run

def w15 : List Bool → List Sym
  | [] => []
  | b::W => (if b then S 5 else S 1)::w15 W

def ac (s : Raw140ERSuffix.Tail) : Nat := match s with | .t11511 => 1 | _ => 0

def TA : Nat → List Sym
  | 0 => []
  | n+1 => S 1::S 1::S 5::TA n

theorem w15_append (W V : List Bool) : w15 (W++V) = w15 W ++ w15 V := by
  induction W with
  | nil => rfl
  | cons b W ih => simp only [List.cons_append,w15,ih]

theorem w15_one (k : Nat) : w15 (List.replicate k false) = U 1 k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [w15,U,List.replicate_succ,ih]

def tr15 : Nat → List Bool
  | 0 => []
  | n+1 => [false,false,true] ++ tr15 n

theorem w15_tr (k : Nat) : w15 (tr15 k) = TA k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [tr15,TA,w15,ite_true,Bool.false_eq_true,ite_false,List.cons_append,List.nil_append,ih]

theorem tail (X : List Sym) (s : Raw140ERSuffix.Tail) :
    Reach base (boundary 4 true (S 1::X) (Raw140ERSuffix.tailWord s))
      (boundary 4 false X (S 1::(TA (ac s) ++ Raw140ERSuffix.tailWord (Raw140ERSuffix.rho s)))) := by
  cases s
  · exact ⟨_,tail542 X []⟩
  · exact ⟨_,tail152 X []⟩
  · exact ⟨_,tail1121 X []⟩
  · exact ⟨_,tail5215 X []⟩
  · exact ⟨_,tail1155 X []⟩
  · exact ⟨_,tail11511 X []⟩

theorem bounce (W : List Bool) (X : List Sym) (s : Raw140ERSuffix.Tail) :
    Reach base (boundary 4 true (S 1::X) (w15 W ++ Raw140ERSuffix.tailWord s))
      (boundary 4 false X (S 1::(w15 W ++ TA (ac s) ++ Raw140ERSuffix.tailWord (Raw140ERSuffix.rho s)))) := by
  induction W generalizing X with
  | nil => simpa [w15] using tail X s
  | cons b W ih =>
    cases b
    · have h0 := Raw140ERSweep.one X (w15 W ++ Raw140ERSuffix.tailWord s)
      have h1 := ih (S 3::X)
      have h2 := stepL base 4 4 false (S 3) (S 1) 3 X (S 1::(w15 W ++ TA (ac s) ++ Raw140ERSuffix.tailWord (Raw140ERSuffix.rho s))) (by rfl)
      exact Reach.trans (Reach.trans ⟨_,h0⟩ h1) ⟨_,h2⟩
    · have h0 := stepR base 4 4 true (S 5) (S 1) 7 (S 1::X) (w15 W ++ Raw140ERSuffix.tailWord s) (by rfl)
      have h1 := ih (S 1::X)
      have h2 := back5 X (w15 W ++ TA (ac s) ++ Raw140ERSuffix.tailWord (Raw140ERSuffix.rho s))
      exact Reach.trans (Reach.trans ⟨_,h0⟩ h1) ⟨_,h2⟩

theorem mixTail (W : List Bool) (X : List Sym) (s : Raw140ERSuffix.Tail) :
    Reach base (boundary 2 true (S 4::X) (S 4::S 0::S 5::(w15 W ++ Raw140ERSuffix.tailWord s)))
      (boundary 3 false (S 5::X) (S 2::S 1::S 1::(w15 W ++ TA (ac s) ++ Raw140ERSuffix.tailWord (Raw140ERSuffix.rho s)))) := by
  have h0 := front X (w15 W ++ Raw140ERSuffix.tailWord s)
  have h1 := bounce W (S 2::S 5::S 5::X) s
  have h2 := finish X (S 1::(w15 W ++ TA (ac s) ++ Raw140ERSuffix.tailWord (Raw140ERSuffix.rho s)))
  exact Reach.trans (Reach.trans ⟨_,h0⟩ h1) ⟨_,h2⟩
#print axioms bounce
#print axioms mixTail
end Raw14042AWord
