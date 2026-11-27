import Raw140ERSweep
import Raw140ERSuffixLocal
namespace Raw140ERSuffix
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double Raw140ERSweep Raw140ERSuffixLocal
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
attribute [local irreducible] boundary run

theorem prepareCarry (k : Nat) (X Y : List Sym) :
    run base (5+3*(k+1)) (boundary 4 false (U 3 (k+1) ++ S 1::X) Y) =
      some (boundary 4 true (S 3::X) (U 1 (k+1) ++ Y)) := by
  have h₁ := sweepL base 4 (S 3) (S 1) 3 (k+1) (S 1::X) Y (by rfl)
  have h₂ := stepL base 4 3 true (S 1) (S 7) 3 X (U 1 (k+1) ++ Y) (by rfl)
  have h₃ := stepR base 3 4 false (S 1) (S 1) 1 (S 7::X) (U 1 k ++ Y) (by rfl)
  have h₄ := stepL base 4 4 true (S 7) (S 3) 1 X (S 1::(U 1 k ++ Y)) (by rfl)
  have h := join (join (join h₁ h₂) h₃) h₄
  simpa only [U,List.replicate_succ,List.cons_append,
    show (k+1)*3+3+1+1=5+3*(k+1) by omega] using h

-- Partial rotation retains k leading 1s on the right. No assumption on Y.
theorem partialRotate (W : List Bool) (k : Nat) (X Y : List Sym) :
    run base (22*W.length+3*k+23)
      (boundary 4 false (U 3 (k+1) ++ oddword W ++ S 5::X) Y) =
      some (boundary 4 true (S 1::(oddword W ++ S 3::X)) (U 1 k ++ Y)) := by
  induction W generalizing k Y with
  | nil =>
    have h₁ := sweepL base 4 (S 3) (S 1) 3 (k+1) (S 5::X) Y (by rfl)
    have h₂ := stepL base 4 4 true (S 5) (S 1) 1 X (U 1 (k+1) ++ Y) (by rfl)
    have h₃ := one X (U 1 k ++ Y)
    have h := join (join h₁ h₂) h₃
    simpa only [oddword,List.nil_append,List.append_assoc,List.length_nil,U,List.replicate_succ,List.cons_append,
      show (k+1)*3+1+19=22*0+3*k+23 by omega] using h
  | cons b W ih =>
    cases b
    · have h₁ := prepareCarry k (oddword W ++ S 5::X) Y
      have h₂ := rotate_one W X (U 1 k ++ Y)
      have h := join h₁ h₂
      simpa only [oddword,Bool.false_eq_true,ite_false,List.length_cons,List.append_assoc,U,List.replicate_succ,List.cons_append,
        show 5+3*(k+1)+(22*(1+W.length)+15)=22*(W.length+1)+3*k+23 by omega] using h
    · have h₁ := ih (k+1) Y
      have h₂ := one (oddword W ++ S 3::X) (U 1 k ++ Y)
      have h := join h₁ h₂
      simpa only [oddword,ite_true,List.length_cons,List.append_assoc,U,List.replicate_succ,List.cons_append,rep_cons,
        show 22*W.length+3*(k+1)+23+19=22*(W.length+1)+3*k+23 by omega] using h

inductive Tail where
  | t542 | t152 | t1121 | t5215 | t1155 | t11511
  deriving DecidableEq, Repr

def tailWord : Tail → List Sym
  | .t542 => [S 5,S 4,S 2]
  | .t152 => [S 1,S 5,S 2]
  | .t1121 => [S 1,S 1,S 2,S 1]
  | .t5215 => [S 5,S 2,S 1,S 5]
  | .t1155 => [S 1,S 1,S 5,S 5]
  | .t11511 => [S 1,S 1,S 5,S 1,S 1]
def rho : Tail → Tail
  | .t542 => .t152
  | .t152 => .t1121
  | .t1121 => .t5215
  | .t5215 => .t1155
  | .t1155 => .t11511
  | .t11511 => .t542
def carry : Tail → List Bool
  | .t11511 => [false,true,true]
  | _ => []
def cost : Tail → Nat
  | .t542 => 50
  | .t152 => 74
  | .t1121 => 88
  | .t5215 => 60
  | .t1155 => 116
  | .t11511 => 183

theorem advance (W : List Bool) (X : List Sym) (s : Tail) :
    run base (22*W.length+cost s)
      (boundary 4 true (S 1::(oddword W ++ S 5::X)) (tailWord s)) =
      some (boundary 4 true (S 1::(oddword (carry s) ++ oddword W ++ S 3::X)) (tailWord (rho s))) := by
  cases s with
  | t542 =>
    have h := join (prep542 (oddword W ++ S 5::X)) (partialRotate W 1 X [S 5,S 2])
    simpa [tailWord,rho,cost,carry,oddword,U,show 24+(22*W.length+3*1+23)=22*W.length+50 by omega] using h
  | t152 =>
    have h := join (prep152 (oddword W ++ S 5::X)) (partialRotate W 1 X [S 1,S 2,S 1])
    simpa [tailWord,rho,cost,carry,oddword,U,show 48+(22*W.length+3*1+23)=22*W.length+74 by omega] using h
  | t1121 =>
    have h := join (prep1121 (oddword W ++ S 5::X)) (partialRotate W 0 X [S 5,S 2,S 1,S 5])
    simpa [tailWord,rho,cost,carry,oddword,U,show 65+(22*W.length+3*0+23)=22*W.length+88 by omega] using h
  | t5215 =>
    have h := join (prep5215 (oddword W ++ S 5::X)) (partialRotate W 0 X [S 1,S 1,S 5,S 5])
    simpa [tailWord,rho,cost,carry,oddword,U,show 37+(22*W.length+3*0+23)=22*W.length+60 by omega] using h
  | t1155 =>
    have h := join (prep1155 (oddword W ++ S 5::X)) (partialRotate W 2 X [S 5,S 1,S 1])
    simpa [tailWord,rho,cost,carry,oddword,U,show 87+(22*W.length+3*2+23)=22*W.length+116 by omega] using h
  | t11511 =>
    have h₁ := join (prep11511 (oddword W ++ S 5::X)) (partialRotate W 2 X [S 5,S 5,S 4,S 2])
    have h₂ := many 2 (oddword W ++ S 3::X) [S 5,S 5,S 4,S 2]
    have h₃ := stepR base 4 4 true (S 5) (S 1) 7
      (S 1::S 3::S 3::(oddword W ++ S 3::X)) [S 5,S 4,S 2] (by rfl)
    have h := join (join h₁ h₂) h₃
    simpa [tailWord,rho,cost,carry,oddword,U,show 109+(22*W.length+3*2+23)+19*2+7=22*W.length+183 by omega] using h

theorem oddword_append (A B : List Bool) : oddword (A++B)=oddword A++oddword B := by
  induction A with
  | nil => rfl
  | cons a A ih => simp only [List.cons_append,oddword,ih]

def advanceWord (W : List Bool) (s : Tail) : List Bool := carry s ++ W ++ [true]

def iterate : Nat → List Bool → Tail → List Bool × Tail
  | 0,W,s => (W,s)
  | n+1,W,s => iterate n (advanceWord W s) (rho s)

theorem bank (n : Nat) (W : List Bool) (X : List Sym) (s : Tail) :
    Reach base (boundary 4 true (S 1::(oddword W ++ U 5 n ++ X)) (tailWord s))
      (boundary 4 true (S 1::(oddword (iterate n W s).1 ++ X)) (tailWord (iterate n W s).2)) := by
  induction n generalizing W s with
  | zero => simpa [iterate,U] using Reach.refl base (boundary 4 true (S 1::(oddword W ++ X)) (tailWord s))
  | succ n ih =>
    have h₁ := advance W (U 5 n ++ X) s
    have h₂ := ih (advanceWord W s) (rho s)
    have h₃ : Reach base (boundary 4 true (S 1::(oddword W ++ U 5 (n+1) ++ X)) (tailWord s))
        (boundary 4 true (S 1::(oddword (advanceWord W s) ++ U 5 n ++ X)) (tailWord (rho s))) := by
      refine ⟨_,?_⟩
      simpa only [advanceWord,oddword_append,oddword,ite_true,U,List.replicate_succ,List.cons_append,List.append_assoc,List.nil_append] using h₁
    exact Reach.trans h₃ h₂

#print axioms partialRotate
#print axioms advance
#print axioms bank
end Raw140ERSuffix
