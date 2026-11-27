import Raw140ERSuffix
namespace Raw140ERExit
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140ERSweep Raw140ERSuffix Raw140ERSuffixLocal
open Raw140Double (Reach)
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
attribute [local irreducible] boundary run

def trip133 : Nat → List Sym
  | 0 => []
  | n+1 => S 1::S 3::S 3::trip133 n
def trip115 : Nat → List Sym
  | 0 => []
  | n+1 => S 1::S 1::S 5::trip115 n

theorem trip115_snoc (n : Nat) :
    trip115 (n+1) = trip115 n ++ [S 1,S 1,S 5] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (S 1::S 1::S 5::trip115 (n+1)) = (S 1::S 1::S 5::trip115 n) ++ [S 1,S 1,S 5]
    simp only [List.cons_append,ih]

theorem pump (n : Nat) (X Y : List Sym) :
    run base (21*n)
      (boundary 4 true (S 3::S 3::S 3::(trip133 n ++ X)) (S 1::S 1::S 1::S 5::Y)) =
    some (boundary 4 true (S 3::S 3::S 3::X) (S 1::S 1::S 1::S 5::(trip115 n ++ Y))) := by
  induction n generalizing Y with
  | zero => simp [trip133,trip115,run]
  | succ n ih =>
    have h₁ := tripLoop (trip133 n ++ X) (S 1::S 1::S 5::Y)
    have h₂ := ih (S 1::S 1::S 5::Y)
    have h := join h₁ h₂
    simpa only [trip133,trip115_snoc,List.cons_append,List.append_assoc,List.nil_append,
      show (7+3*3+3+1+1)+21*n=21*(n+1) by omega] using h

theorem exitCost (p : Nat) (Y : List Sym) :
    run base (36*p+298) (boundary 4 true (U 3 (p+3) ++ [S 2]) (S 1::S 1::S 1::S 5::Y)) =
      some (boundary 0 true (U 3 (p+11) ++ [S 2]) Y) := by
  have h := finishBank p Y
  have hc : 7+(p+3)*3+3+1+(p+4)*3+5+(p+4)*3+5+(p+5)*3+1+(p+6)*3+3+(p+6)*3+3+1+1+7+(p+7)*3+3+1+(p+8)*3+5+(p+8)*3+5+(p+9)*3+1+(p+10)*3+3+(p+11)*3 = 36*p+298 := by omega
  rw [hc] at h
  exact h

theorem startExit (j n p : Nat) (Y : List Sym) :
    Reach base
      (boundary 4 false (U 3 (j+1) ++ trip133 (n+2) ++ U 3 p ++ [S 2]) Y)
      (boundary 0 true (U 3 (p+11) ++ [S 2]) (trip115 n ++ U 1 j ++ Y)) := by
  let X := U 3 p ++ [S 2]
  have h₁ := prepareCarry j (S 3::S 3::S 1::S 3::S 3::(trip133 n ++ X)) Y
  have h₂ := tripLoop (trip133 n ++ X) (U 1 j ++ Y)
  have h₃ := pump n X (U 1 j ++ Y)
  have h₄ := exitCost p (trip115 n ++ U 1 j ++ Y)
  refine ⟨5+3*(j+1)+(7+3*3+3+1+1)+21*n+(36*p+298),?_⟩
  have h₁' : run base (5+3*(j+1))
      (boundary 4 false (U 3 (j+1) ++ trip133 (n+2) ++ X) Y) =
      some (boundary 4 true (S 3::S 3::S 3::S 1::S 3::S 3::(trip133 n ++ X)) (S 1::(U 1 j ++ Y))) := by
    simpa only [trip133,U,List.replicate_succ,List.cons_append,List.append_assoc] using h₁
  have h₃' : run base (21*n)
      (boundary 4 true (S 3::S 3::S 3::(trip133 n ++ X)) (S 1::S 1::S 1::S 5::(U 1 j ++ Y))) =
      some (boundary 4 true (U 3 (p+3) ++ [S 2]) (S 1::S 1::S 1::S 5::(trip115 n ++ U 1 j ++ Y))) := by
    simpa only [X,U,List.replicate_succ,List.cons_append,List.append_assoc] using h₃
  have h := join (join (join h₁' h₂) h₃') h₄
  simpa only [X,List.append_assoc] using h

-- For a depleted left bank, convert its 133 carry triplets into 115 triplets.
-- At least two carry triplets are required. Last suffix gains one extra triplet.
def extra : Tail → Nat
  | .t11511 => 1
  | _ => 0
theorem exitBank (n p : Nat) (s : Tail) :
    Reach base
      (boundary 4 true (S 1::(trip133 (n+2) ++ U 3 p ++ [S 2])) (tailWord s))
      (boundary 0 true (U 3 (p+11) ++ [S 2]) (trip115 (n+extra s) ++ tailWord (rho s))) := by
  let X := trip133 (n+2) ++ U 3 p ++ [S 2]
  cases s with
  | t542 =>
    have h₁ := prep542 X
    have h₂ := startExit 1 n p [S 5,S 2]
    exact Reach.trans ⟨_,h₁⟩ h₂
  | t152 =>
    have h₁ := prep152 X
    have h₂ := startExit 1 n p [S 1,S 2,S 1]
    exact Reach.trans ⟨_,h₁⟩ h₂
  | t1121 =>
    have h₁ := prep1121 X
    have h₂ := startExit 0 n p [S 5,S 2,S 1,S 5]
    exact Reach.trans ⟨_,h₁⟩ h₂
  | t5215 =>
    have h₁ := prep5215 X
    have h₂ := startExit 0 n p [S 1,S 1,S 5,S 5]
    exact Reach.trans ⟨_,h₁⟩ h₂
  | t1155 =>
    have h₁ := prep1155 X
    have h₂ := startExit 2 n p [S 5,S 1,S 1]
    exact Reach.trans ⟨_,h₁⟩ h₂
  | t11511 =>
    have h₁ := prep11511 X
    have h₂ := startExit 2 n p [S 5,S 5,S 4,S 2]
    have h := Reach.trans ⟨_,h₁⟩ h₂
    simpa only [extra,rho,tailWord,trip115_snoc,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.append_assoc,List.nil_append] using h

#print axioms pump
#print axioms exitBank
end Raw140ERExit
