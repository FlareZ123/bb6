import Raw14042CounterLocal
import Raw140DoubleCore
namespace Raw14042Counter
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double Raw14042CounterLocal Raw140VariantTransfer
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
attribute [local irreducible] boundary run

def T : Nat → List Sym
  | 0 => []
  | n+1 => S 3::S 2::S 2::T n

def B : Nat → List Sym
  | 0 => []
  | n+1 => B n ++ [S 6,S 6,S 2]

theorem bank_cons (n : Nat) : B (n+1) = S 6::S 6::S 2::B n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change B (n+1) ++ [S 6,S 6,S 2] = S 6::S 6::S 2::(B n ++ [S 6,S 6,S 2])
    simp only [ih,List.cons_append]

theorem trip_snoc (n : Nat) : T (n+1) = T n ++ [S 3,S 2,S 2] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change S 3::S 2::S 2::T (n+1) = (S 3::S 2::S 2::T n) ++ [S 3,S 2,S 2]
    simp only [List.cons_append,ih]

theorem Tadd (n m : Nat) : T (n+m) = T n ++ T m := by
  induction m with
  | zero => simp [T]
  | succ m ih => simp only [Nat.add_succ,trip_snoc,ih,List.append_assoc]

theorem scanTwo (m : Nat) (X Y : List Sym) :
    Reach base (boundary 4 true (S 2::X) (S 3::(U 2 m ++ Y)))
      (boundary 4 true (S 2::(U 6 m ++ X)) (S 3::Y)) := by
  induction m generalizing X with
  | zero => exact Reach.refl base _
  | succ m ih =>
    have h0 : Reach base (boundary 4 true (S 2::X) (S 3::S 2::(U 2 m ++ Y)))
        (boundary 4 true (S 2::S 6::X) (S 3::(U 2 m ++ Y))) :=
      ⟨_,forwardOne X (U 2 m ++ Y)⟩
    have h1 := ih (S 6::X)
    simpa only [U,List.replicate_succ,List.cons_append,rep_cons] using Reach.trans h0 h1

theorem scanTrip (n : Nat) (X Y : List Sym) :
    Reach base (boundary 4 true (S 2::X) (S 3::(T n ++ Y)))
      (boundary 4 true (S 2::(B n ++ X)) (S 3::Y)) := by
  induction n generalizing X with
  | zero => exact Reach.refl base _
  | succ n ih =>
    have h0 : Reach base (boundary 4 true (S 2::X) (S 3::S 3::S 2::S 2::(T n ++ Y)))
        (boundary 4 true (S 2::S 6::S 6::S 2::X) (S 3::(T n ++ Y))) :=
      ⟨_,forwardTrip X (T n ++ Y)⟩
    have h1 := ih (S 6::S 6::S 2::X)
    simpa only [T,B,List.cons_append,List.append_assoc,List.nil_append] using Reach.trans h0 h1

theorem back (n : Nat) (X Y : List Sym) :
    Reach base (boundary 1 false (B n ++ X) (S 2::S 2::S 3::Y))
      (boundary 1 false X (S 2::S 2::(T n ++ S 3::Y))) := by
  induction n generalizing Y with
  | zero => exact Reach.refl base _
  | succ n ih =>
    have h0 : Reach base (boundary 1 false (S 6::S 6::S 2::(B n ++ X)) (S 2::S 2::S 3::Y))
        (boundary 1 false (B n ++ X) (S 2::S 2::S 3::S 2::S 2::S 3::Y)) :=
      ⟨_,backTrip (B n ++ X) Y⟩
    have h1 := ih (S 2::S 2::S 3::Y)
    simpa only [bank_cons,trip_snoc,List.cons_append,List.append_assoc,List.nil_append] using Reach.trans h0 h1

inductive CTail
  | c31 | c32 | c315 | c325 | c3242 | c35221
  deriving DecidableEq, Repr

def cword : CTail → List Sym
  | .c31 => [S 3,S 1]
  | .c32 => [S 3,S 2]
  | .c315 => [S 3,S 1,S 5]
  | .c325 => [S 3,S 2,S 5]
  | .c3242 => [S 3,S 2,S 4,S 2]
  | .c35221 => [S 3,S 5,S 2,S 2,S 1]

def next : CTail → CTail
  | .c31 => .c32
  | .c32 => .c315
  | .c315 => .c325
  | .c325 => .c3242
  | .c3242 => .c35221
  | .c35221 => .c31

def ccarry : CTail → Nat
  | .c35221 => 1
  | _ => 0

theorem cstart (s : CTail) : ∃ Y, cword s = S 3::Y := by
  cases s <;> exact ⟨_,rfl⟩

theorem prep (s : CTail) (X : List Sym) :
    Reach base (boundary 4 true (S 2::X) (S 3::cword s))
      (boundary 1 false X (S 2::S 2::(T (ccarry s) ++ cword (next s)))) := by
  cases s with
  | c31 => exact ⟨_,prep31 X⟩
  | c32 => exact ⟨_,prep32 X⟩
  | c315 => exact ⟨_,prep315 X⟩
  | c325 => exact ⟨_,prep325 X⟩
  | c3242 => exact ⟨_,prep3242 X⟩
  | c35221 => exact ⟨_,prep35221 X⟩

theorem backAll (n m : Nat) (X : List Sym) (s : CTail) :
    Reach base (boundary 1 false (B n ++ U 6 m ++ X) (S 2::S 2::(T (ccarry s) ++ cword (next s))))
      (boundary 1 false X (U 2 m ++ S 2::S 2::(T (n+ccarry s) ++ cword (next s)))) := by
  have hs : ∃ Y, T (ccarry s) ++ cword (next s) = S 3::Y := by
    cases s <;> exact ⟨_,rfl⟩
  obtain ⟨Y,hY⟩ := hs
  have h0 := back n (U 6 m ++ X) Y
  have h1 := sweepL base 1 (S 6) (S 2) 3 m X (S 2::S 2::(T n ++ S 3::Y)) (by rfl)
  have h := Reach.trans h0 (⟨_,h1⟩ : Reach base _ _)
  rw [Tadd,hY]
  simpa only [hY,List.append_assoc,ite_true,U] using h

def counterCfg (m n : Nat) (X : List Sym) (s : CTail) : Prim :=
  boundary 4 true (S 2::S 7::X) (S 3::(U 2 m ++ T n ++ cword s))

theorem counterStep (m n : Nat) (X : List Sym) (s : CTail) :
    Reach base (counterCfg m n (S 3::X) s) (counterCfg (m+1) (n+ccarry s) X (next s)) := by
  let Z := S 7::S 3::X
  have h0 := scanTwo m Z (T n ++ cword s)
  have h1 := scanTrip n (U 6 m ++ Z) (cword s)
  have h2 := prep s (B n ++ U 6 m ++ Z)
  have h3 := backAll n m Z s
  have h4 := finishStep X (U 2 m ++ T (n+ccarry s) ++ cword (next s))
  have h := Reach.trans (Reach.trans (Reach.trans h0 h1) h2) h3
  -- The leading m twos commute with the two boundary twos.
  have he : U 2 m ++ S 2::S 2::(T (n+ccarry s) ++ cword (next s)) =
      S 2::S 2::(U 2 m ++ T (n+ccarry s) ++ cword (next s)) := by
    induction m with
    | zero => rfl
    | succ m ih => simp only [U,List.replicate_succ,List.cons_append] at *; rw [ih]
  rw [he] at h
  have h5 : Reach base _ _ := ⟨_,h4⟩
  simpa only [counterCfg,Z,U,List.replicate_succ,List.cons_append,List.append_assoc] using Reach.trans h h5

def turn : Nat → CTail → Nat × CTail
  | 0,s => (0,s)
  | k+1,s => (ccarry s + (turn k (next s)).1,(turn k (next s)).2)

theorem counterIter (k m n : Nat) (X : List Sym) (s : CTail) :
    Reach base (counterCfg m n (U 3 k ++ X) s)
      (counterCfg (m+k) (n+(turn k s).1) X (turn k s).2) := by
  induction k generalizing m n s with
  | zero => simpa [U,turn] using Reach.refl base (counterCfg m n X s)
  | succ k ih =>
    have h0 := counterStep m n (U 3 k ++ X) s
    have h1 := ih (m+1) (n+ccarry s) (next s)
    simpa only [U,List.replicate_succ,List.cons_append,turn,
      show m+1+k=m+(k+1) by omega,Nat.add_assoc] using Reach.trans h0 h1

#print axioms counterStep
#print axioms counterIter
end Raw14042Counter
