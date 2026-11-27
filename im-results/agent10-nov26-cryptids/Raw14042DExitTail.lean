import Raw14042DExit
import Raw14042DExitAffine
import Raw14042Bank
namespace Raw14042DExitTail
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double Raw14042DExitAffine
open Raw14042Bank (B T bank_cons pumpAny)
open Raw140ERSuffix (prepareCarry)
open Raw140ERSuffixLocal (prep1121 prep5215)
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
attribute [local irreducible] boundary run
abbrev R := Reach base
abbrev A (p : Nat) (Y : List Sym) := boundary 0 true (U 3 p ++ [S 2]) Y
abbrev ER (X Y : List Sym) := boundary 4 true X Y
abbrev EL (X Y : List Sym) := boundary 4 false X Y
abbrev BR (p : Nat) (Y : List Sym) := boundary 1 true (U 5 p) Y

theorem ua (b m n : Nat) : U b (m+n) = U b m ++ U b n := by
  induction m with
  | zero => simp [U]
  | succ m ih => simp only [U,Nat.succ_add,List.replicate_succ,List.cons_append] at ih ⊢; rw [ih]
theorem tcons (n : Nat) : T (n+1) = S 1::S 1::S 5::T n := rfl

theorem absorb (j p : Nat) (Y : List Sym) :
    R (A p (S 0::(U 1 (2*j) ++ Y))) (A (p+4*j) (S 0::Y)) := by
  induction j generalizing p with
  | zero => exact Reach.refl base _
  | succ j ih =>
    have h0 := oddPump p (U 1 (2*j) ++ Y)
    have h1 := ih (p+4)
    simpa only [R,A,Raw140VariantTransfer.Mbase,U,List.replicate_succ,List.cons_append,show 2*(j+1)=2*j+1+1 by omega,show p+4+4*j=p+4*(j+1) by omega] using Reach.trans ⟨_,h0⟩ h1

theorem absorbStart (j : Nat) (Y : List Sym) :
    R (ER [S 2] (U 1 (2*j+2) ++ Y)) (A (4*j+3) (S 0::Y)) := by
  have h0 := oddStart (U 1 (2*j) ++ Y)
  have h1 := absorb j 3 Y
  simpa only [R,A,ER,Raw140VariantTransfer.Mbase,U,List.replicate_succ,List.cons_append,show 3+4*j=4*j+1+1+1 by omega,show 4*j+3=4*j+1+1+1 by omega,rep_cons] using Reach.trans ⟨_,h0⟩ h1

theorem absorbER (j p : Nat) (Y : List Sym) :
    R (ER (U 3 p ++ [S 2]) (U 1 (2*j+2) ++ Y)) (A (p+4*j+3) (S 0::Y)) := by
  have h0 := erTwo p (U 1 (2*j) ++ Y)
  have h1 := absorb j (p+3) Y
  simpa only [R,A,ER,Raw140VariantTransfer.Mbase,U,List.replicate_succ,List.cons_append,show p+3+4*j=p+4*j+1+1+1 by omega,show p+4*j+3=p+4*j+1+1+1 by omega,rep_cons] using Reach.trans ⟨_,h0⟩ h1

-- Transfer N+1 triplets, turn a suffix which gives exactly one leading 3,
-- and repack all but one triplet before the arbitrary context X.
theorem pack (N : Nat) (X Y : List Sym) :
    R (EL (S 3::(B (N+1) ++ X)) Y) (ER (S 3::S 3::S 3::X) (S 1::(T N ++ Y))) := by
  have h0 := prepareCarry 0 (S 3::S 3::(B N ++ X)) Y
  have h1 := pumpAny N X Y
  exact ⟨_,by simpa only [ER,EL,bank_cons,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append] using join h0 h1⟩

theorem pack1121 (N : Nat) (X : List Sym) :
    R (ER (S 1::X) (T (N+1) ++ [S 1,S 1,S 2,S 1]))
      (ER (S 3::S 3::S 3::X) (S 1::(T N ++ [S 5,S 2,S 1,S 5]))) := by
  have h0 := Raw140VariantTransfer.erMany base (by intro a b c h; exact h) (N+1) X [S 1,S 1,S 2,S 1]
  have h1 := prep1121 (B (N+1) ++ X)
  have h2 := pack N X [S 5,S 2,S 1,S 5]
  exact Reach.trans ⟨_,join h0 h1⟩ h2

theorem pack5215 (N : Nat) (X : List Sym) :
    R (ER (S 1::X) (T (N+1) ++ [S 5,S 2,S 1,S 5]))
      (ER (S 3::S 3::S 3::X) (S 1::(T N ++ [S 1,S 1,S 5,S 5]))) := by
  have h0 := Raw140VariantTransfer.erMany base (by intro a b c h; exact h) (N+1) X [S 5,S 2,S 1,S 5]
  have h1 := prep5215 (B (N+1) ++ X)
  have h2 := pack N X [S 1,S 1,S 5,S 5]
  exact Reach.trans ⟨_,join h0 h1⟩ h2

-- A word 1^m 55 1^b 5 is transferred through the head, and all
-- triplets survive the 1121 -> 5215 tail change.
theorem firstPack (m b N : Nat) :
    R (ER [S 1] (U 1 m ++ S 5::S 5::(U 1 (b+1) ++ S 5::(T (N+1) ++ [S 1,S 1,S 2,S 1]))))
      (ER [S 2] (U 1 (m+1) ++ S 5::S 5::(U 1 (b+1) ++ S 5::(T (N+1) ++ [S 5,S 2,S 1,S 5])))) := by
  let Z := T (N+1) ++ [S 1,S 1,S 2,S 1]
  let X := U 3 m
  let W := U 3 (b+1) ++ S 1::S 1::X
  let Y := T (N+1) ++ [S 5,S 2,S 1,S 5]
  have h0 := Raw140ERSweep.many m [] (S 5::S 5::(U 1 (b+1) ++ S 5::Z))
  have h1 := sweepR base 4 (S 5) (S 1) 7 2 (S 1::X) (U 1 (b+1) ++ S 5::Z) (by rfl)
  have h2 := Raw140ERSweep.many (b+1) (S 1::S 1::X) (S 5::Z)
  have h3 := stepR base 4 4 true (S 5) (S 1) 7 (S 1::W) Z (by rfl)
  have h4 := pack1121 N (S 1::W)
  have h5 := Raw140ERSweep.carry 2 W (T N ++ [S 5,S 2,S 1,S 5])
  have h6 := Raw140ERSweep.carry (b+1) (S 1::X) (T (N+1) ++ [S 5,S 2,S 1,S 5])
  have h7 := Raw140ERSweep.carry 0 X (U 1 (b+1) ++ S 5::Y)
  have h8 := oddInit m (S 5::(U 1 (b+1) ++ S 5::Y))
  have h01 := join h0 (by simpa only [X,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_nil] using h1)
  have h02 := join h01 h2
  have h03 := join h02 h3
  have h04 := Reach.trans (⟨_,h03⟩ : R _ _) h4
  have h05 := Reach.trans h04 (⟨_,h5⟩ : R _ _)
  have h06 := Reach.trans h05 (⟨_,by simpa only [W,Y,tcons,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.append_assoc,List.nil_append] using h6⟩ : R _ _)
  have h07 := Reach.trans h06 (⟨_,by simpa only [X,Y,tcons,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] using h7⟩ : R _ _)
  exact Reach.trans h07 ⟨_,by simpa only [ER,Raw140VariantTransfer.Mbase,X,Y,tcons,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.append_nil,List.nil_append,List.append_assoc] using h8⟩

theorem secondPack (p b N : Nat) :
    R (ER (S 1::S 1::(U 3 p ++ [S 2])) (U 1 (b+1) ++ S 5::(T (N+1) ++ [S 5,S 2,S 1,S 5])))
      (ER (U 3 (p+1) ++ [S 2]) (U 1 (b+2) ++ S 5::(T (N+2) ++ [S 5]))) := by
  let Z := T (N+1) ++ [S 5,S 2,S 1,S 5]
  let X := U 3 p ++ [S 2]
  let W := U 3 (b+1) ++ S 1::X
  have h0 := Raw140ERSweep.many (b+1) (S 1::X) (S 5::Z)
  have h1 := stepR base 4 4 true (S 5) (S 1) 7 (S 1::W) Z (by rfl)
  have h2 := pack5215 N (S 1::W)
  have h3 := Raw140ERSweep.carry 2 W (T N ++ [S 1,S 1,S 5,S 5])
  have h4 := Raw140ERSweep.carry (b+1) X (T (N+1) ++ [S 1,S 1,S 5,S 5])
  have h01 := join h0 h1
  have h02 := Reach.trans (⟨_,h01⟩ : R _ _) h2
  have h03 := Reach.trans h02 (⟨_,h3⟩ : R _ _)
  have h04 := Reach.trans h03 (⟨_,by simpa only [W,tcons,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] using h4⟩ : R _ _)
  have et : S 1::S 1::S 5::(T N ++ [S 1,S 1,S 5,S 5]) = T (N+2) ++ [S 5] := by
    rw [Raw14042Bank.trip_snoc (N+1)]
    simp only [tcons,List.append_assoc,List.cons_append,List.nil_append]
  simpa only [R,ER,X,Z,U,List.replicate_succ,List.cons_append,List.nil_append,List.append_assoc,et] using h04

theorem lastPack (p N : Nat) :
    R (ER (S 1::(U 3 p ++ [S 2])) (T (N+2) ++ [S 5]))
      (A (p+11) (T N ++ [S 1,S 1])) := by
  let X := U 3 p ++ [S 2]
  have h0 := Raw140VariantTransfer.erMany base (by intro a b c h; exact h) (N+2) X [S 5]
  have h1 := Raw14042DExitLocal.prep5 (B (N+2) ++ X) []
  have h2 := stepL base 4 3 true (S 1) (S 7) 3 (S 3::S 3::(B (N+1) ++ X)) [S 1,S 1,S 1] (by rfl)
  have h3 := stepR base 3 4 false (S 1) (S 1) 1 (S 7::S 3::S 3::(B (N+1) ++ X)) [S 1,S 1] (by rfl)
  have h4 := stepL base 4 4 true (S 7) (S 3) 1 (S 3::S 3::(B (N+1) ++ X)) [S 1,S 1,S 1] (by rfl)
  have h5 := pumpAny (N+1) X [S 1,S 1]
  have h6 := erOne (p+3) (T (N+1) ++ [S 1,S 1])
  have h7 := bOne (p+6) (S 1::S 5::(T N ++ [S 1,S 1]))
  have h8 := oddFinish (p+6) (T N ++ [S 1,S 1])
  have h01 := join h0 h1
  rw [bank_cons (N+1)] at h01
  have h02 := join h01 h2
  have h05 := join (join (join h02 h3) h4) h5
  have h06 := join h05 (by simpa only [X,U,List.replicate_succ,List.cons_append,Raw140VariantTransfer.Mbase] using h6)
  have h07 := join h06 (by simpa only [tcons,U,List.replicate_succ,List.cons_append,Raw140VariantTransfer.Mbase] using h7)
  have h08 := join h07 h8
  exact ⟨_,by simpa only [A,ER,X,Raw140VariantTransfer.Mbase,show p+6+5=p+11 by omega] using h08⟩

-- m=2i+1 and b=2j+1. N+1 triplets at the entry, N at the exit.
theorem evenWordExit (i j N : Nat) :
    R (ER [S 1] (U 1 (2*i+1) ++ S 5::S 5::(U 1 (2*j+1) ++ S 5::(T (N+1) ++ [S 1,S 1,S 2,S 1]))))
      (A (4*i+4*j+20) (T N ++ [S 1,S 1])) := by
  let Y := U 1 (2*j+1) ++ S 5::(T (N+1) ++ [S 5,S 2,S 1,S 5])
  have h0 := firstPack (2*i+1) (2*j) N
  have h1 := absorbStart i (S 5::S 5::Y)
  have h2 := ar055 (4*i+3) Y
  have h3 := secondPack (4*i+4) (2*j) N
  have h4 := absorbER j (4*i+5) (S 5::(T (N+2) ++ [S 5]))
  have h5 := ar05 (4*i+4*j+8) (T (N+2) ++ [S 5])
  have h6 := lastPack (4*i+4*j+9) N
  have h01 := Reach.trans h0 (by simpa only [Y,show 2*i+1+1=2*i+2 by omega] using h1)
  have h02 := Reach.trans h01 (⟨_,h2⟩ : R _ _)
  have h03 := Reach.trans h02 (by simpa only [Y,show 4*i+3+1=4*i+4 by omega] using h3)
  have h04 := Reach.trans h03 (by simpa only [show 4*i+4+1=4*i+5 by omega] using h4)
  have h05 := Reach.trans h04 (⟨_,by simpa only [A,Raw140VariantTransfer.Mbase,show 4*i+5+4*j+3=4*i+4*j+8 by omega] using h5⟩ : R _ _)
  exact Reach.trans h05 (by simpa only [show 4*i+4*j+8+1=4*i+4*j+9 by omega,show 4*i+4*j+9+11=4*i+4*j+20 by omega] using h6)
#print axioms evenWordExit
end Raw14042DExitTail
