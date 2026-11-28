import Raw14037DOdd
namespace Raw14037WordReturn
open BB6BlockFAR Raw140Orbit Raw140Extra
open Raw140Double (Reach)
open Raw140ERSuffix Raw140ERExit Raw140ERSuffixLocal
open Raw14037DOdd (pumpAny turn)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
attribute [local irreducible] boundary run

theorem prepSweep (j n m : Nat) (X Y : List Sym) :
    Reach base (boundary 4 false (U 3 (j+1) ++ trip133 n ++ U 3 m ++ X) Y)
      (boundary 4 false X (U 1 (m+1) ++ trip115 n ++ U 1 j ++ Y)) := by
  cases n with
  | zero =>
    simp only [trip133,trip115,List.append_nil,List.append_assoc,merge]
    have h := sweepL base 4 (S 3) (S 1) 3 (j+1+m) X Y (by rfl)
    exact ⟨_,by simpa only [merge, show j+1+m=m+1+j by omega] using h⟩
  | succ n =>
    let Z := U 3 m ++ X
    have h0 := prepareCarry j (S 3::S 3::(trip133 n ++ Z)) Y
    have h1 := pumpAny n Z (U 1 j ++ Y)
    have h2 := stepR base 4 4 false (S 1) (S 5) 7 (S 3::S 3::S 3::Z) (trip115 n ++ U 1 j ++ Y) (by rfl)
    have h3 := sweepL base 4 (S 3) (S 1) 3 (m+3) X (S 5::(trip115 n ++ U 1 j ++ Y)) (by rfl)
    simp only [Z,U,List.replicate_succ,List.cons_append,trip133,List.append_assoc,Bool.false_eq_true,ite_false,ite_true] at h0 h1 h2 h3
    have h := Reach.trans (Reach.trans (Reach.trans ⟨_,h0⟩ ⟨_,h1⟩) ⟨_,h2⟩) ⟨_,h3⟩
    simpa only [U,List.replicate_succ,List.cons_append,trip133,trip115,List.append_assoc,Z,rep_cons] using h

theorem rotateSweep (n m : Nat) (s : Tail) (X : List Sym) :
    Reach base (boundary 4 true (S 1::(trip133 n ++ U 3 m ++ X)) (tailWord s))
      (boundary 4 false X (U 1 (m+1) ++ trip115 (n+extra s) ++ tailWord (rho s))) := by
  let Z := trip133 n ++ U 3 m ++ X
  cases s with
  | t542 =>
    have h0 := prep542 Z
    have h1 := prepSweep 1 n m X [S 5,S 2]
    simp only [Z,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h0 h1
    simpa only [extra,rho,tailWord,trip115_snoc,Nat.add_zero,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.append_assoc,List.nil_append] using Reach.trans ⟨_,h0⟩ h1
  | t152 =>
    have h0 := prep152 Z
    have h1 := prepSweep 1 n m X [S 1,S 2,S 1]
    simp only [Z,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h0 h1
    simpa only [extra,rho,tailWord,trip115_snoc,Nat.add_zero,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.append_assoc,List.nil_append] using Reach.trans ⟨_,h0⟩ h1
  | t1121 =>
    have h0 := prep1121 Z
    have h1 := prepSweep 0 n m X [S 5,S 2,S 1,S 5]
    simp only [Z,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h0 h1
    simpa only [extra,rho,tailWord,trip115_snoc,Nat.add_zero,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.append_assoc,List.nil_append] using Reach.trans ⟨_,h0⟩ h1
  | t5215 =>
    have h0 := prep5215 Z
    have h1 := prepSweep 0 n m X [S 1,S 1,S 5,S 5]
    simp only [Z,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h0 h1
    simpa only [extra,rho,tailWord,trip115_snoc,Nat.add_zero,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.append_assoc,List.nil_append] using Reach.trans ⟨_,h0⟩ h1
  | t1155 =>
    have h0 := prep1155 Z
    have h1 := prepSweep 2 n m X [S 5,S 1,S 1]
    simp only [Z,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h0 h1
    simpa only [extra,rho,tailWord,trip115_snoc,Nat.add_zero,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.append_assoc,List.nil_append] using Reach.trans ⟨_,h0⟩ h1
  | t11511 =>
    have h0 := prep11511 Z
    have h1 := prepSweep 2 n m X [S 5,S 5,S 4,S 2]
    simp only [Z,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h0 h1
    simpa only [extra,rho,tailWord,trip115_snoc,Nat.add_zero,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.append_assoc,List.nil_append] using Reach.trans ⟨_,h0⟩ h1

def bits133 : Nat → List Bool
  | 0 => []
  | n+1 => false::true::true::bits133 n

theorem bits133_map (n : Nat) : Raw140ERSweep.oddword (bits133 n) = trip133 n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [bits133,Raw140ERSweep.oddword,trip133,ite_true,ite_false,Bool.false_eq_true,ih]

theorem bits3_map (m : Nat) : Raw140ERSweep.oddword (List.replicate m true) = U 3 m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [U,List.replicate_succ,Raw140ERSweep.oddword,ite_true,ih]

theorem carry_map (s : Tail) : Raw140ERSweep.oddword (carry s) = trip133 (extra s) := by cases s <;> rfl

theorem trip133_add (n m : Nat) : trip133 (n+m) = trip133 n ++ trip133 m := by
  induction n with
  | zero => simp [trip133]
  | succ n ih => simp only [show n+1+m=n+m+1 by omega,trip133,ih,List.cons_append]

theorem bankOne (n m : Nat) (s : Tail) (X : List Sym) :
    Reach base (boundary 4 true (S 1::(trip133 n ++ U 3 m ++ S 5::X)) (tailWord s))
      (boundary 4 true (S 1::(trip133 (n+extra s) ++ U 3 (m+1) ++ X)) (tailWord (rho s))) := by
  have h := Raw140ERSuffix.advance (bits133 n ++ List.replicate m true) X s
  simp only [oddword_append,bits133_map,bits3_map,carry_map,List.append_assoc,rep_cons] at h
  have he : trip133 (extra s) ++ (trip133 n ++ S 3::(U 3 m ++ X)) = trip133 (n+extra s) ++ (U 3 (m+1) ++ X) := by
    rw [← List.append_assoc,← trip133_add,Nat.add_comm (extra s) n]
    rfl
  rw [he] at h
  exact ⟨_,by simpa only [List.append_assoc] using h⟩

theorem bankMany (k n m : Nat) (s : Tail) (X : List Sym) :
    Reach base (boundary 4 true (S 1::(trip133 n ++ U 3 m ++ U 5 k ++ X)) (tailWord s))
      (boundary 4 true (S 1::(trip133 (n+(turn k s).1) ++ U 3 (m+k) ++ X)) (tailWord (turn k s).2)) := by
  induction k generalizing n m s with
  | zero => simpa [turn,U] using Reach.refl base (boundary 4 true (S 1::(trip133 n ++ U 3 m ++ X)) (tailWord s))
  | succ k ih =>
    have h0 := bankOne n m s (U 5 k ++ X)
    have h1 := ih (n+extra s) (m+1) (rho s)
    have h := Reach.trans (by simpa only [List.append_assoc] using h0) (by simpa only [List.append_assoc] using h1)
    simpa only [turn,U,List.replicate_succ,List.cons_append,List.append_assoc,
      show m+1+k=m+(k+1) by omega,Nat.add_assoc] using h

#print axioms rotateSweep
#print axioms bankMany
end Raw14037WordReturn
