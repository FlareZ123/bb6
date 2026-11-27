import Raw140ERSuffix
import Raw140VariantTransfer
namespace Raw14042Bank
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140ERSuffix Raw140ERSuffixLocal
open Raw140Double (Reach)
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
attribute [local irreducible] boundary run

abbrev B := Raw140VariantTransfer.bank
abbrev T := Raw140VariantTransfer.trip

theorem bank_cons (n : Nat) : B (n+1) = S 1::S 3::S 3::B n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change B (n+1) ++ [S 1,S 3,S 3] = S 1::S 3::S 3::(B n ++ [S 1,S 3,S 3])
    rw [ih]

theorem trip_snoc (n : Nat) : T (n+1) = T n ++ [S 1,S 1,S 5] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change S 1::S 1::S 5::T (n+1) = (S 1::S 1::S 5::T n) ++ [S 1,S 1,S 5]
    simp only [List.cons_append,ih]

-- This stronger pump has only one fixed leading 1, not 1115.
theorem pumpAny (n : Nat) (X Y : List Sym) :
    run base (21*n)
      (boundary 4 true (S 3::S 3::S 3::(B n ++ X)) (S 1::Y)) =
    some (boundary 4 true (S 3::S 3::S 3::X) (S 1::(T n ++ Y))) := by
  induction n generalizing Y with
  | zero => simp [B,T,Raw140VariantTransfer.bank,Raw140VariantTransfer.trip,run]
  | succ n ih =>
    have h₁ := tripLoop (B n ++ X) Y
    have h₂ := ih (S 1::S 1::S 5::Y)
    have h := join h₁ h₂
    simpa only [bank_cons,trip_snoc,List.cons_append,List.append_assoc,List.nil_append,
      show (7+3*3+3+1+1)+21*n=21*(n+1) by omega] using h

-- p is one less than the actual positive length of the 3-bank.
theorem start42 (j n p : Nat) (Y : List Sym) :
    Reach base
      (boundary 4 false (U 3 (j+1) ++ B (n+1) ++ [S 2,S 5] ++ U 3 (p+1) ++ [S 2]) Y)
      (boundary 0 true (U 3 (p+13) ++ [S 2]) (T n ++ U 1 j ++ Y)) := by
  let X := S 2::S 5::(U 3 (p+1) ++ [S 2])
  have h₁ := prepareCarry j (S 3::S 3::(B n ++ X)) Y
  have h₂ := pumpAny n X (U 1 j ++ Y)
  have h₃ := finish42Any p (T n ++ U 1 j ++ Y)
  have h := join (join h₁ h₂) h₃
  refine ⟨_, ?_⟩
  simpa only [X,bank_cons,U,List.replicate_succ,List.cons_append,List.append_assoc,
    List.nil_append] using h

def extra : Tail → Nat
  | .t11511 => 1
  | _ => 0

theorem exit42 (n p : Nat) (s : Tail) :
    Reach base
      (boundary 4 true (S 1::(B (n+1) ++ [S 2,S 5] ++ U 3 (p+1) ++ [S 2])) (tailWord s))
      (boundary 0 true (U 3 (p+13) ++ [S 2]) (T (n+extra s) ++ tailWord (rho s))) := by
  cases s with
  | t542 =>
    have h₁ := prep542 (B (n+1) ++ ([S 2,S 5] ++ U 3 (p+1) ++ [S 2]))
    have h₂ := start42 1 n p [S 5,S 2]
    simp only [U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h₂
    have h := Reach.trans ⟨_,h₁⟩ h₂
    simpa only [extra,rho,tailWord,Nat.add_zero,trip_snoc,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] using h
  | t152 =>
    have h₁ := prep152 (B (n+1) ++ ([S 2,S 5] ++ U 3 (p+1) ++ [S 2]))
    have h₂ := start42 1 n p [S 1,S 2,S 1]
    simp only [U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h₂
    have h := Reach.trans ⟨_,h₁⟩ h₂
    simpa only [extra,rho,tailWord,Nat.add_zero,trip_snoc,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] using h
  | t1121 =>
    have h₁ := prep1121 (B (n+1) ++ ([S 2,S 5] ++ U 3 (p+1) ++ [S 2]))
    have h₂ := start42 0 n p [S 5,S 2,S 1,S 5]
    simp only [U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h₂
    have h := Reach.trans ⟨_,h₁⟩ h₂
    simpa only [extra,rho,tailWord,Nat.add_zero,trip_snoc,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] using h
  | t5215 =>
    have h₁ := prep5215 (B (n+1) ++ ([S 2,S 5] ++ U 3 (p+1) ++ [S 2]))
    have h₂ := start42 0 n p [S 1,S 1,S 5,S 5]
    simp only [U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h₂
    have h := Reach.trans ⟨_,h₁⟩ h₂
    simpa only [extra,rho,tailWord,Nat.add_zero,trip_snoc,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] using h
  | t1155 =>
    have h₁ := prep1155 (B (n+1) ++ ([S 2,S 5] ++ U 3 (p+1) ++ [S 2]))
    have h₂ := start42 2 n p [S 5,S 1,S 1]
    simp only [U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h₂
    have h := Reach.trans ⟨_,h₁⟩ h₂
    simpa only [extra,rho,tailWord,Nat.add_zero,trip_snoc,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] using h
  | t11511 =>
    have h₁ := prep11511 (B (n+1) ++ ([S 2,S 5] ++ U 3 (p+1) ++ [S 2]))
    have h₂ := start42 2 n p [S 5,S 5,S 4,S 2]
    simp only [U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h₂
    have h := Reach.trans ⟨_,h₁⟩ h₂
    simpa only [extra,rho,tailWord,Nat.add_zero,trip_snoc,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] using h

-- The input has n+2 triplets and p+1 threes; no restriction n>0.
theorem return42 (n p : Nat) (s : Tail) :
    Reach Raw140VariantTransfer.M42
      (boundary 0 true (U 3 (p+1) ++ [S 2]) (T (n+2) ++ tailWord s))
      (boundary 0 true (U 3 (p+13) ++ [S 2]) (T (n+extra s) ++ tailWord (rho s))) := by
  have h₁ := Raw140VariantTransfer.transferMany42 (n+1) (U 3 (p+1) ++ [S 2]) (tailWord s)
  have h₂ := (exit42 n p s).ext (fill_extends _ _)
  have h₁' : Reach Raw140VariantTransfer.M42
      (boundary 0 true (U 3 (p+1) ++ [S 2]) (T (n+2) ++ tailWord s))
      (boundary 4 true (S 1::(B (n+1) ++ [S 2,S 5] ++ U 3 (p+1) ++ [S 2])) (tailWord s)) := by
    refine ⟨_, ?_⟩
    simpa only [T,B,Raw140VariantTransfer.trip,List.cons_append,List.nil_append,List.append_assoc] using h₁
  exact Reach.trans h₁' h₂

#print axioms pumpAny
#print axioms start42
#print axioms exit42
#print axioms return42
end Raw14042Bank
