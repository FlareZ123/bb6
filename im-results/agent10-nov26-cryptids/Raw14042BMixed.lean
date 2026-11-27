import Raw14042BMixedLocal
import Raw140ERSweep
namespace Raw14042BMixed
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double Raw14042Counter Raw14042BMixedLocal
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
attribute [local irreducible] boundary run

def Q (a b n : Nat) (X : List Sym) (s : CTail) : Prim :=
  boundary 4 true (S 1::X) (U 1 a ++ S 5::(U 2 b ++ T n ++ cword s))

theorem half1 (a b : Nat) (X Y : List Sym) :
    Reach base (boundary 4 true (S 1::S 5::X) (U 1 a ++ S 5::S 2::S 2::(U 2 b ++ Y)))
      (boundary 4 true (S 1::X) (U 1 (a+2) ++ S 2::S 3::(U 2 b ++ Y))) := by
  let Z := U 3 a ++ S 5::X
  let V := U 2 b ++ Y
  have h0 := Raw140ERSweep.many a (S 5::X) (S 5::S 2::S 2::V)
  have h1 := stepR base 4 4 true (S 5) (S 1) 7 (S 1::Z) (S 2::S 2::V) (by rfl)
  have h2 := Raw14042BMixedLocal.h1 Z V
  have h3 := sweepL base 4 (S 3) (S 1) 3 (a+1) (S 5::X) (S 1::S 2::S 3::V) (by rfl)
  have h4 := stepL base 4 4 true (S 5) (S 1) 1 X (U 1 (a+1) ++ S 1::S 2::S 3::V) (by rfl)
  have h01 := join h0 h1
  have h02 := join h01 h2
  have h03 := join h02 (by simpa only [Z,U,List.replicate_succ,List.cons_append] using h3)
  have h04 := join h03 h4
  exact ⟨_,by simpa only [V,U,List.replicate_succ,List.cons_append,rep_cons,ite_true] using h04⟩

theorem half2 (a b n : Nat) (X : List Sym) (s : CTail) :
    Reach base (boundary 4 true (S 1::S 5::X) (U 1 (a+2) ++ S 2::S 3::(U 2 b ++ T n ++ cword s)))
      (Q (a+1) (b+3) (n+ccarry s) X (next s)) := by
  let Z := S 5::(U 3 (a+2) ++ S 5::X)
  let V := T (n+ccarry s) ++ cword (next s)
  have h0 := Raw140ERSweep.many (a+2) (S 5::X) (S 2::S 3::(U 2 b ++ T n ++ cword s))
  have h1 := Raw14042BMixedLocal.h2 (U 3 (a+2) ++ S 5::X) (U 2 b ++ T n ++ cword s)
  have h2 := scanTwo b Z (T n ++ cword s)
  have h3 := scanTrip n (U 6 b ++ Z) (cword s)
  have h4 := prep s (B n ++ U 6 b ++ Z)
  have h5 := backAll n b Z s
  have h6 := Raw14042BMixedLocal.h3 (U 3 (a+1) ++ S 5::X) (U 2 b ++ S 2::S 2::V)
  -- h3 local first puts one extra 2, then a 5 at the right.
  have h7 := sweepL base 4 (S 3) (S 1) 3 (a+1) (S 5::X) (S 5::S 2::(U 2 b ++ S 2::S 2::V)) (by rfl)
  have h8 := stepL base 4 4 true (S 5) (S 1) 1 X (U 1 (a+1) ++ S 5::S 2::(U 2 b ++ S 2::S 2::V)) (by rfl)
  have h01 : Reach base _ _ := ⟨_,join h0 h1⟩
  simp only [List.append_assoc] at h01 h2 h3 h4 h5 h6
  have h05 := Reach.trans (Reach.trans (Reach.trans (Reach.trans h01 h2) h3) h4) h5
  have h06 : Reach base _ _ := Reach.trans h05 ⟨_,by simpa only [Z,V,U,List.replicate_succ,List.cons_append,List.append_assoc] using h6⟩
  have h08 := Reach.trans h06 ⟨_,join h7 h8⟩
  simpa only [Q,V,U,List.replicate_succ,List.cons_append,rep_cons,List.append_assoc,ite_true] using h08

theorem pair (a b n : Nat) (X : List Sym) (s : CTail) :
    Reach base (Q a (b+2) n (S 5::S 5::X) s) (Q (a+1) (b+3) (n+ccarry s) X (next s)) := by
  have h := half1 a b (S 5::X) (T n ++ cword s)
  have h' := half2 a b n X s
  simp only [List.append_assoc] at h h'
  simpa only [Q,U,List.replicate_succ,List.cons_append,List.append_assoc] using Reach.trans h h'

theorem pairs (k a b n : Nat) (X : List Sym) (s : CTail) :
    Reach base (Q a (b+2) n (U 5 (2*k) ++ X) s)
      (Q (a+k) (b+2+k) (n+(Raw14042Counter.turn k s).1) X (Raw14042Counter.turn k s).2) := by
  induction k generalizing a b n s with
  | zero => simpa [U,Raw14042Counter.turn] using Reach.refl base (Q a (b+2) n X s)
  | succ k ih =>
    have h0 := pair a b n (U 5 (2*k) ++ X) s
    have h1 := ih (a+1) (b+1) (n+ccarry s) (next s)
    simpa only [U,List.replicate_succ,List.cons_append,Raw14042Counter.turn,
      show 2*(k+1)=2*k+2 by omega,show a+1+k=a+(k+1) by omega,
      show b+1+2+k=b+2+(k+1) by omega,Nat.add_assoc] using Reach.trans h0 h1
#print axioms pair
#print axioms pairs
end Raw14042BMixed
