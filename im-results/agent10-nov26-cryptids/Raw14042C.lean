import Raw14042Counter
import Raw14042LowLocal
namespace Raw14042C
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double Raw14042Counter Raw14042CounterLocal Raw14042LowLocal Raw140VariantTransfer
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
attribute [local irreducible] boundary run

def C (p n : Nat) (s : CTail) : Prim :=
  boundary 0 true (U 3 p ++ [S 2]) (S 2::(T n ++ cword s))

theorem consumeC (p n : Nat) (s : CTail) :
    Reach base (boundary 0 true (S 4::U 6 (p+1) ++ [S 4]) (S 2::S 2::(T (n+1) ++ cword s)))
      (boundary 0 true (U 3 (p+3) ++ [S 2]) (U 2 5 ++ T (n+ccarry s) ++ cword (next s))) := by
  let X := S 5::S 2::(U 6 (p+1) ++ [S 4])
  have h0 : Reach base
      (boundary 0 true (S 4::U 6 (p+1) ++ [S 4]) (S 2::S 2::(T (n+1) ++ cword s)))
      (boundary 4 true (S 2::X) (S 3::S 2::S 2::(T n ++ cword s))) := by
    refine ⟨_,?_⟩
    simpa only [X,T,U,List.replicate_succ,List.cons_append,List.append_assoc] using
      initC (U 6 p ++ [S 4]) (S 2::S 2::(T n ++ cword s))
  have h1 := scanTwo 2 X (T n ++ cword s)
  have h2 := scanTrip n (U 6 2 ++ X) (cword s)
  have h3 := prep s (B n ++ U 6 2 ++ X)
  have h4 := backAll n 2 X s
  have h5 : Reach base
      (boundary 1 false X (U 2 4 ++ T (n+ccarry s) ++ cword (next s)))
      (boundary 0 true (U 3 (p+3) ++ [S 2]) (U 2 5 ++ T (n+ccarry s) ++ cword (next s))) := by
    refine ⟨_,?_⟩
    simpa only [X,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc,
      show p+1+2=p+3 by omega] using finishC (p+1) (T (n+ccarry s) ++ cword (next s))
  simp only [X,U,List.append_assoc,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append] at h0 h1 h2 h3 h4 h5
  exact Reach.trans (Reach.trans (Reach.trans (Reach.trans (Reach.trans h0 h1) h2) h3) h4) h5

theorem pumpTwo2 (p : Nat) (Y : List Sym) :
    Reach base (boundary 0 true (U 3 p ++ [S 2]) (U 2 5 ++ Y))
      (boundary 0 true (U 3 (p+8) ++ [S 2]) (S 2::Y)) := by
  have h0 := twoPump p (S 2::S 2::Y)
  have h1 := twoPump (p+4) Y
  refine ⟨_,?_⟩
  simpa only [U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,
      show p+4+4=p+8 by omega] using join h0 h1

theorem returnC (p n : Nat) (s : CTail) :
    Reach M42 (C p (n+2) s) (C (p+12) (n+ccarry s) (next s)) := by
  have e : Extends M42 := fill_extends _ _
  have h0 : Reach M42 (C p (n+2) s)
      (boundary 0 true (S 4::U 6 (p+2) ++ [S 4]) (S 2::S 2::(T (n+1) ++ cword s))) := by
    refine ⟨_,?_⟩
    simpa only [C,T,U,List.replicate_succ,List.cons_append,List.append_assoc] using
      boundaryOne p (S 2::S 2::(T (n+1) ++ cword s))
  have h1 := Reach.ext e (consumeC (p+1) n s)
  have h2 := Reach.ext e (pumpTwo2 (p+4) (T (n+ccarry s) ++ cword (next s)))
  simpa only [C,List.append_assoc,show p+1+1=p+2 by omega,show p+1+3=p+4 by omega,
      show p+4+8=p+12 by omega] using Reach.trans (Reach.trans h0 h1) h2

theorem low315 (p : Nat) : Reach M42 (C p 1 .c315)
    (boundary 0 true (U 3 (p+13) ++ [S 2]) [S 2]) := by
  exact ⟨_,Raw14042LowLocal.lowC315 p⟩

#print axioms returnC
#print axioms low315
end Raw14042C
