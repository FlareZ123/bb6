import Raw14042WordLocal
namespace Raw14042Word
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double Raw14042Counter Raw14042CounterLocal Raw14042WordLocal
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
attribute [local irreducible] boundary run

def w23 : List Bool → List Sym
  | [] => []
  | b::W => (if b then S 3 else S 2)::w23 W

theorem w23_append (W V : List Bool) : w23 (W++V) = w23 W ++ w23 V := by
  induction W with
  | nil => rfl
  | cons b W ih => simp only [List.cons_append,w23,ih]

theorem w23_two (k : Nat) : w23 (List.replicate k false) = U 2 k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [w23,U,List.replicate_succ,ih]

def trip23 : Nat → List Bool
  | 0 => []
  | n+1 => [true,false,false] ++ trip23 n

theorem word_trip23 (k : Nat) : w23 (trip23 k) = T k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [trip23,T,w23_append,w23,ite_true,Bool.false_eq_true,ite_false,List.cons_append,List.nil_append,ih]

theorem trip23_add (m n : Nat) : trip23 (m+n) = trip23 m ++ trip23 n := by
  induction m with
  | zero => simp [trip23]
  | succ m ih => simp [Nat.succ_add,trip23,ih,List.append_assoc]

theorem bounce (W : List Bool) (X : List Sym) (s : CTail) :
    Reach base (boundary 4 true (S 2::X) (S 3::(w23 W ++ cword s)))
      (boundary 1 false X (S 2::S 2::(w23 W ++ T (ccarry s) ++ cword (next s)))) := by
  induction W generalizing X with
  | nil => simpa [w23] using prep s X
  | cons b W ih =>
    cases b
    · have h0 := forwardOne X (w23 W ++ cword s)
      have h1 := ih (S 6::X)
      have h2 := stepL base 1 1 false (S 6) (S 2) 3 X (S 2::S 2::(w23 W ++ T (ccarry s) ++ cword (next s))) (by rfl)
      exact Reach.trans (Reach.trans ⟨_,h0⟩ h1) ⟨_,h2⟩
    · have h0 := forward3 X (w23 W ++ cword s)
      have h1 := ih (S 2::X)
      have h2 := back3 X (w23 W ++ T (ccarry s) ++ cword (next s))
      exact Reach.trans (Reach.trans ⟨_,h0⟩ h1) ⟨_,h2⟩

def Cfg (X : List Sym) (W : List Bool) (s : CTail) : Prim :=
  boundary 4 true (S 2::S 7::X) (S 3::(w23 W ++ cword s))

theorem step (X : List Sym) (W : List Bool) (s : CTail) :
    Reach base (Cfg (S 3::X) W s)
      (Cfg X (false::(W ++ trip23 (ccarry s))) (next s)) := by
  have h0 := bounce W (S 7::S 3::X) s
  have h1 := finishStep X (w23 W ++ T (ccarry s) ++ cword (next s))
  have h := Reach.trans h0 (⟨_,h1⟩ : Reach base _ _)
  simpa only [Cfg,w23,w23_append,word_trip23,List.append_assoc,Bool.false_eq_true,ite_false,List.cons_append] using h

theorem iter (k : Nat) (X : List Sym) (W : List Bool) (s : CTail) :
    Reach base (Cfg (U 3 k ++ X) W s)
      (Cfg X (List.replicate k false ++ W ++ trip23 (Raw14042Counter.turn k s).1) (Raw14042Counter.turn k s).2) := by
  induction k generalizing W s with
  | zero => simpa [U,Raw14042Counter.turn,trip23] using Reach.refl base (Cfg X W s)
  | succ k ih =>
    have h0 := step (U 3 k ++ X) W s
    have h1 := ih (false::(W ++ trip23 (ccarry s))) (next s)
    have h := Reach.trans h0 h1
    have e : List.replicate (k+1) false = List.replicate k false ++ [false] := by rw [List.replicate_succ']
    rw [e]
    simpa only [U,List.replicate_succ,List.cons_append,Raw14042Counter.turn,← trip23_add,List.append_assoc,List.singleton_append,List.nil_append] using h

theorem deplete (W : List Bool) (s : CTail) :
    Reach base (Cfg [S 2] W s)
      (boundary 1 false [] (S 2::S 2::S 2::S 2::(w23 W ++ T (Raw14042Counter.turn 2 s).1 ++ cword (Raw14042Counter.turn 2 s).2))) := by
  let Z := w23 W ++ T (ccarry s) ++ cword (next s)
  have h0 := bounce W [S 7,S 2] s
  have h1 := finishZero Z
  have h2 := bounce (false::(W ++ trip23 (ccarry s))) [S 6] (next s)
  have h3 : Reach base _ _ := Reach.trans (Reach.trans h0 (⟨_,h1⟩ : Reach base _ _)) (by simpa only [Z,w23,w23_append,word_trip23,List.append_assoc,Bool.false_eq_true,ite_false,List.cons_append] using h2)
  have h4 := stepL base 1 1 false (S 6) (S 2) 3 [] (S 2::S 2::(w23 (false::(W ++ trip23 (ccarry s))) ++ T (ccarry (next s)) ++ cword (next (next s)))) (by rfl)
  simp only [w23,w23_append,word_trip23,List.append_assoc,Bool.false_eq_true,ite_false,List.cons_append] at h4
  have h := Reach.trans h3 (⟨_,h4⟩ : Reach base _ _)
  simpa only [Cfg,w23,w23_append,word_trip23,List.append_assoc,Bool.false_eq_true,ite_false,List.cons_append,Tadd,Raw14042Counter.turn,Nat.add_zero] using h
#print axioms bounce
#print axioms step
#print axioms iter
#print axioms deplete
end Raw14042Word
