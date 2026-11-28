import Raw14037SixBank
import Raw14042Counter
namespace Raw14037Counter
open BB6BlockFAR Raw140Orbit Raw140Extra
open Raw140Double (Reach)
open Raw14042Counter Raw14042CounterLocal
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] boundary run

def G (v : Nat) (X R : List Sym) : Prim :=
  boundary 3 true (S 6::S 2::(U 6 v ++ S 7::X)) R

theorem cancel5 {a b c : Prim} {n : Nat}
    (h : run base 5 a = some b) (g : run base (5+n) a = some c) : run base n b = some c := by
  rw [run_add,h] at g
  exact g

theorem prepAfter (s : CTail) (X : List Sym) :
    Reach base (boundary 3 true (S 6::S 2::X) (cword s))
      (boundary 1 false X (S 2::S 2::(T (ccarry s) ++ cword (next s)))) := by
  have h := stepR base 4 3 true (S 3) (S 6) 5 (S 2::X) (cword s) (by rfl)
  cases s with
  | c31 => exact ⟨_,cancel5 (n := 49) h (prep31 X)⟩
  | c32 => exact ⟨_,cancel5 (n := 71) h (prep32 X)⟩
  | c315 => exact ⟨_,cancel5 (n := 49) h (prep315 X)⟩
  | c325 => exact ⟨_,cancel5 (n := 73) h (prep325 X)⟩
  | c3242 => exact ⟨_,cancel5 (n := 87) h (prep3242 X)⟩
  | c35221 => exact ⟨_,cancel5 (n := 59) h (prep35221 X)⟩

theorem scanPrep (n : Nat) (s : CTail) (X : List Sym) :
    Reach base (boundary 3 true (S 6::S 2::X) (T n ++ cword s))
      (boundary 1 false (B n ++ X) (S 2::S 2::(T (ccarry s) ++ cword (next s)))) := by
  cases n with
  | zero => simpa only [T,B,List.nil_append] using prepAfter s X
  | succ n =>
    have h0 := stepR base 4 3 true (S 3) (S 6) 5 (S 2::X) (S 3::S 2::S 2::(T n ++ cword s)) (by rfl)
    have h1 := forwardTrip X (T n ++ cword s)
    have h2 := cancel5 (n := 40) h0 h1
    have h3 := scanTrip n (S 6::S 6::S 2::X) (cword s)
    have h4 := prep s (B n ++ S 6::S 6::S 2::X)
    have h := Reach.trans (Reach.trans ⟨_,h2⟩ h3) h4
    simpa only [T,B,List.cons_append,List.append_assoc,List.nil_append,ite_true] using h

theorem advance (v n : Nat) (s : CTail) (X : List Sym) :
    Reach base (G v (S 3::X) (T n ++ cword s))
      (G (v+1) X (T (n+ccarry s) ++ cword (next s))) := by
  let Z := S 7::S 3::X
  have h0 := scanPrep n s (U 6 v ++ Z)
  have h1 := backAll n v Z s
  let R := T (n+ccarry s) ++ cword (next s)
  have h2 : Reach base (G v (S 3::X) (T n ++ cword s))
      (boundary 1 false Z (U 2 (v+2) ++ R)) := by
    simp only [List.append_assoc] at h0 h1
    have h := Reach.trans h0 h1
    simpa only [G,Z,R,U,List.replicate_succ,List.cons_append,List.append_assoc,rep_cons] using h
  have h3 := Raw14037SixBank.seed X (U 2 (v+1) ++ R)
  have h4 := Raw14037SixBank.loopMany (v+1) (S 7::X) R
  have h5 := join h3 h4
  have h6 : Reach base (boundary 1 false Z (U 2 (v+2) ++ R))
      (G (v+1) X R) := by exact ⟨_,h5⟩
  exact Reach.trans h2 h6

theorem iterate (k v n : Nat) (s : CTail) (X : List Sym) :
    Reach base (G v (U 3 k ++ X) (T n ++ cword s))
      (G (v+k) X (T (n+(turn k s).1) ++ cword (turn k s).2)) := by
  induction k generalizing v n s with
  | zero => simpa [U,turn] using Reach.refl base (G v X (T n ++ cword s))
  | succ k ih =>
    have h0 := advance v n s (U 3 k ++ X)
    have h1 := ih (v+1) (n+ccarry s) (next s)
    simpa only [U,List.replicate_succ,List.cons_append,turn,
      show v+1+k=v+(k+1) by omega,Nat.add_assoc] using Reach.trans h0 h1

theorem deplete (v n : Nat) (s : CTail) :
    Reach base (G v [S 2] (T n ++ cword s))
      (boundary 1 false [] (U 2 (v+4) ++ T (n+ccarry s+ccarry (next s)) ++ cword (next (next s)))) := by
  let Z := [S 7,S 2]
  let m := n+ccarry s
  let r := next s
  let R := T m ++ cword r
  have h0 := scanPrep n s (U 6 v ++ Z)
  have h1 := backAll n v Z s
  have h2 : Reach base (G v [S 2] (T n ++ cword s))
      (boundary 1 false Z (U 2 (v+2) ++ R)) := by
    simp only [List.append_assoc] at h0 h1
    simpa only [G,Z,R,m,r,U,List.replicate_succ,List.cons_append,List.append_assoc,rep_cons] using Reach.trans h0 h1
  have h3 : Reach base (boundary 1 false Z (U 2 (v+2) ++ R))
      (boundary 4 true [S 2,S 6] (S 3::(U 2 (v+1) ++ R))) := by
    exact ⟨_,finishZero (U 2 v ++ R)⟩
  have h4 : Reach base (boundary 4 true [S 2,S 6] (S 3::(U 2 (v+1) ++ R)))
      (boundary 4 true (S 2::U 6 (v+2)) (S 3::R)) := by
    simpa only [U,List.replicate_succ,rep_cons,List.cons_append,List.append_nil] using scanTwo (v+1) [S 6] R
  have h5 := scanTrip m (U 6 (v+2)) (cword r)
  have h6 := prep r (B m ++ U 6 (v+2))
  have h7 := backAll m (v+2) [] r
  simp only [List.append_nil] at h7
  have h8 := Reach.trans (Reach.trans (Reach.trans (Reach.trans (Reach.trans h2 h3) h4) h5) h6) h7
  simpa only [Z,m,r,R,U,List.replicate_succ,rep_cons,List.cons_append,List.append_assoc,List.append_nil,
    show v+2+2=v+4 by omega] using h8

#print axioms deplete
#print axioms advance
#print axioms iterate
end Raw14037Counter
