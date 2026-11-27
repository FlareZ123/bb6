import Raw14042RightLocal
import Raw140DoubleCore
namespace Raw14042Right
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double Raw14042RightLocal Raw140VariantTransfer
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
attribute [local irreducible] boundary run

def T : Nat → List Sym
  | 0 => []
  | n+1 => S 6::S 4::S 4::T n

def B : Nat → List Sym
  | 0 => []
  | n+1 => B n ++ [S 5,S 5,S 4]

theorem bank_cons (n : Nat) : B (n+1) = S 5::S 5::S 4::B n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change B (n+1) ++ [S 5,S 5,S 4] = S 5::S 5::S 4::(B n ++ [S 5,S 5,S 4])
    simp only [ih,List.cons_append]

theorem trip_snoc (n : Nat) : T (n+1) = T n ++ [S 6,S 4,S 4] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change S 6::S 4::S 4::T (n+1) = (S 6::S 4::S 4::T n) ++ [S 6,S 4,S 4]
    simp only [List.cons_append,ih]

theorem scan (n : Nat) (X Y : List Sym) :
    run base (45*n)
      (boundary 2 true (S 4::X) (T n ++ S 6::Y)) =
    some (boundary 2 true (S 4::(B n ++ X)) (S 6::Y)) := by
  induction n generalizing X with
  | zero => simp [T,B,run]
  | succ n ih =>
    cases n with
    | zero => simpa [T,B,Mbase] using rightScanOne X Y
    | succ n =>
      have h0 := rightScanOne X (S 4::S 4::(T n ++ S 6::Y))
      have h1 := ih (S 5::S 5::S 4::X)
      simpa only [Mbase,T,B,List.cons_append,List.append_assoc,List.nil_append,
        show (5+1+1+3+7+1+1+5+1+1+3+7+1+1+5+1+1)+45*(n+1)=45*(n+1+1) by omega] using join h0 h1

theorem pump (n : Nat) (X Y : List Sym) :
    run base (21*n)
      (boundary 3 false (S 5::(B n ++ X)) Y) =
    some (boundary 3 false (S 5::X) (T n ++ Y)) := by
  induction n generalizing Y with
  | zero => simp [T,B,run]
  | succ n ih =>
    have h0 := rightPumpOne (B n ++ X) Y
    have h1 := ih (S 6::S 4::S 4::Y)
    simpa only [Mbase,bank_cons,trip_snoc,List.cons_append,List.append_assoc,List.nil_append,
      show (3*3+7+1+1+3)+21*n=21*(n+1) by omega] using join h0 h1

theorem tailTurn (s : Tail) (X : List Sym) :
    Reach base (boundary 2 true (S 4::X) (tailWord s))
      (boundary 3 false (S 5::X) (T (carry s) ++ tailWord (rho s))) := by
  cases s with
  | s62 => exact ⟨_,tail62 X⟩
  | s64 => exact ⟨_,tail64 X⟩
  | s6221 => exact ⟨_,tail6221 X⟩
  | s6421 => exact ⟨_,tail6421 X⟩
  | s6405 => exact ⟨_,tail6405 X⟩
  | s62542 => exact ⟨_,tail62542 X⟩

theorem Tadd (n m : Nat) : T (n+m) = T n ++ T m := by
  induction m with
  | zero => simp [T]
  | succ m ih => simp only [Nat.add_succ,trip_snoc,ih,List.append_assoc]

theorem start (n p : Nat) (s : Tail) :
    Reach M42 (boundary 1 true (U 5 p) (T (n+2) ++ tailWord s))
      (boundary 2 true (S 4::(B n ++ (S 5::S 5::S 5::S 2::U 5 (p+1)))) (tailWord s)) := by
  have e : Extends M42 := fill_extends _ _
  have hTail : ∃ Y, tailWord s = S 6::Y := by
    cases s <;> exact ⟨_,rfl⟩
  obtain ⟨Y,hY⟩ := hTail
  cases n with
  | zero =>
    refine ⟨80, ?_⟩
    simpa only [T,B,hY,U,List.replicate_succ,List.cons_append,List.nil_append] using rightStart (U 5 p) Y
  | succ n =>
    have h0 := rightStart (U 5 p) (S 4::S 4::(T n ++ S 6::Y))
    have h1 := run_ext M42 e _ _ _ (scan (n+1) (S 5::S 5::S 5::S 2::U 5 (p+1)) Y)
    refine ⟨80+45*(n+1), ?_⟩
    simpa only [T,hY,U,List.replicate_succ,List.cons_append,List.append_assoc,List.nil_append] using join h0 h1

theorem rightReturn42 (n p : Nat) (s : Tail) :
    Reach M42 (boundary 1 true (U 5 p) (T (n+2) ++ tailWord s))
      (boundary 1 true (U 5 (p+12)) (T (n+carry s) ++ tailWord (rho s))) := by
  have e : Extends M42 := fill_extends _ _
  let X := S 5::S 5::S 5::S 2::U 5 (p+1)
  have h0 := start n p s
  have h1 := Reach.ext e (tailTurn s (B n ++ X))
  have h2 := Reach.ext e (⟨21*n,pump n X (T (carry s) ++ tailWord (rho s))⟩ : Reach base _ _)
  have h3 := Reach.ext e (⟨_,rightFinish p (T n ++ (T (carry s) ++ tailWord (rho s)))⟩ : Reach base _ _)
  rw [Tadd n (carry s)]
  simpa only [X,List.append_assoc] using Reach.trans (Reach.trans (Reach.trans h0 h1) h2) h3

#print axioms scan
#print axioms pump
#print axioms rightReturn42
end Raw14042Right
