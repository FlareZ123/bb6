import Raw14042Bank
import Raw14042DExitAffine
namespace Raw14042BGeneral
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double Raw140VariantTransfer Raw14042DExitAffine
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
attribute [local irreducible] boundary run
abbrev R := Reach M42
-- Shared ER bank lemmas factored from Raw14086B; only base is used.
abbrev ATail := Raw140ERSuffix.Tail
abbrev aword := Raw140ERSuffix.tailWord
abbrev an := Raw140ERSuffix.rho
abbrev ac := Raw14042Bank.extra
abbrev AB := Raw14042Bank.B
abbrev TA := Raw14042Bank.T

def arank : ATail → Nat
  | .t542 => 0 | .t152 => 1 | .t1121 => 2 | .t5215 => 3 | .t1155 => 4 | .t11511 => 5

theorem arank_lt (s : ATail) : arank s < 6 := by cases s <;> decide
theorem abalance (s : ATail) : 6*ac s+arank (an s)=arank s+1 := by cases s <;> decide

def aTurn (k : Nat) (s : ATail) : Nat × ATail :=
  match k with
  | 0 => (0,s)
  | k+1 => (ac s+(aTurn k (an s)).1,(aTurn k (an s)).2)

theorem aTurn_balance (k : Nat) (s : ATail) : 6*(aTurn k s).1+arank (aTurn k s).2=k+arank s := by
  induction k generalizing s with
  | zero => simp [aTurn]
  | succ k ih =>
    have h := ih (an s)
    have h' := abalance s
    change 6*(ac s+(aTurn k (an s)).1)+arank (aTurn k (an s)).2=k+1+arank s
    omega

def bw (n : Nat) : List Bool :=
  match n with
  | 0 => []
  | n+1 => false::true::true::bw n

theorem bw_sound (n : Nat) : Raw140ERSweep.oddword (bw n) = AB n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [bw,Raw140ERSweep.oddword,Bool.false_eq_true,ite_false,ite_true,ih,Raw14042Bank.bank_cons]

theorem ow3 (m : Nat) : Raw140ERSweep.oddword (List.replicate m true)=U 3 m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [List.replicate_succ,Raw140ERSweep.oddword,ite_true,ih,U]

theorem carry_word (s : ATail) : Raw140ERSweep.oddword (Raw140ERSuffix.carry s)=AB (ac s) := by
  cases s <;> rfl

theorem ab_add (n m : Nat) : AB (n+m)=AB n ++ AB m := by
  induction m with
  | zero => simp [AB,Raw140VariantTransfer.bank]
  | succ m ih =>
    change AB (n+m) ++ [S 1,S 3,S 3] = AB n ++ (AB m ++ [S 1,S 3,S 3])
    simp only [ih,List.append_assoc]

theorem bankStep (n m : Nat) (X : List Sym) (s : ATail) :
    Reach base
      (boundary 4 true (S 1::(AB n ++ U 3 m ++ S 5::X)) (aword s))
      (boundary 4 true (S 1::(AB (n+ac s) ++ U 3 (m+1) ++ X)) (aword (an s))) := by
  let W := bw n ++ List.replicate m true
  have h := Raw140ERSuffix.advance W X s
  have hw : Raw140ERSweep.oddword W=AB n ++ U 3 m := by
    simp only [W,Raw140ERSuffix.oddword_append,bw_sound,ow3]
  rw [hw,carry_word] at h
  have h' : AB (ac s) ++ AB n = AB (n+ac s) := by rw [← ab_add,Nat.add_comm]
  have he : AB (ac s) ++ (AB n ++ (U 3 m ++ S 3::X)) = AB (n+ac s) ++ (U 3 (m+1) ++ X) := by
    rw [← List.append_assoc (AB (ac s)),h']
    congr 1
    exact merge 3 m 1 X
  refine ⟨22*W.length+Raw140ERSuffix.cost s,?_⟩
  simpa only [List.append_assoc,he,aword,an] using h

theorem bankIter (k n m : Nat) (X : List Sym) (s : ATail) :
    Reach base (boundary 4 true (S 1::(AB n ++ U 3 m ++ U 5 k ++ X)) (aword s))
      (boundary 4 true (S 1::(AB (n+(aTurn k s).1) ++ U 3 (m+k) ++ X)) (aword (aTurn k s).2)) := by
  induction k generalizing n m s with
  | zero =>
    simpa only [aTurn,Nat.add_zero,U,List.replicate_zero,List.append_nil,List.nil_append] using Reach.refl base _
  | succ k ih =>
    have h0 := bankStep n m (U 5 k ++ X) s
    have h1 := ih (n+ac s) (m+1) (an s)
    simp only [List.append_assoc] at h0 h1
    simpa only [aTurn,U,List.replicate_succ,List.cons_append,List.append_assoc,Nat.add_assoc,
      show m+1+k=m+(k+1) by omega] using Reach.trans h0 h1

-- A generic bank exit retaining the homogeneous context, rather than using
-- the final 42-specific defect absorption.
theorem exitFront (j n : Nat) (X Y : List Sym) :
    Reach base
      (boundary 4 false (U 3 (j+1) ++ AB (n+1) ++ X) Y)
      (boundary 4 true (S 3::S 3::S 3::X) (S 1::(TA n ++ U 1 j ++ Y))) := by
  have h0 := Raw140ERSuffix.prepareCarry j (S 3::S 3::(AB n ++ X)) Y
  have h1 := Raw14042Bank.pumpAny n X (U 1 j ++ Y)
  have h := join h0 h1
  refine ⟨5+3*(j+1)+21*n,?_⟩
  simpa only [AB,TA,Raw14042Bank.bank_cons,U,List.replicate_succ,List.cons_append,List.append_assoc,List.nil_append] using h

theorem exitAny (n : Nat) (X : List Sym) (s : ATail) :
    Reach base
      (boundary 4 true (S 1::(AB (n+1) ++ X)) (aword s))
      (boundary 4 true (S 3::S 3::S 3::X) (S 1::(TA (n+ac s) ++ aword (an s)))) := by
  cases s with
  | t542 =>
    have h0 := Raw140ERSuffixLocal.prep542 (AB (n+1) ++ X)
    have h1 := exitFront 1 n X [S 5,S 2]
    simp only [U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h1
    simpa only [Raw14042Bank.extra,aword,an,Raw140ERSuffix.tailWord,Raw140ERSuffix.rho,List.nil_append,Raw140ERSuffix.tailWord,Raw140ERSuffix.rho,Nat.add_zero,List.append_assoc] using Reach.trans (⟨_,h0⟩ : Reach base _ _) h1
  | t152 =>
    have h0 := Raw140ERSuffixLocal.prep152 (AB (n+1) ++ X)
    have h1 := exitFront 1 n X [S 1,S 2,S 1]
    simp only [U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h1
    simpa only [Raw14042Bank.extra,aword,an,Raw140ERSuffix.tailWord,Raw140ERSuffix.rho,List.nil_append,Raw140ERSuffix.tailWord,Raw140ERSuffix.rho,Nat.add_zero,List.append_assoc] using Reach.trans (⟨_,h0⟩ : Reach base _ _) h1
  | t1121 =>
    have h0 := Raw140ERSuffixLocal.prep1121 (AB (n+1) ++ X)
    have h1 := exitFront 0 n X [S 5,S 2,S 1,S 5]
    simp only [U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h1
    simpa only [Raw14042Bank.extra,aword,an,Raw140ERSuffix.tailWord,Raw140ERSuffix.rho,List.nil_append,Raw140ERSuffix.tailWord,Raw140ERSuffix.rho,Nat.add_zero,List.append_assoc] using Reach.trans (⟨_,h0⟩ : Reach base _ _) h1
  | t5215 =>
    have h0 := Raw140ERSuffixLocal.prep5215 (AB (n+1) ++ X)
    have h1 := exitFront 0 n X [S 1,S 1,S 5,S 5]
    simp only [U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h1
    simpa only [Raw14042Bank.extra,aword,an,Raw140ERSuffix.tailWord,Raw140ERSuffix.rho,List.nil_append,Raw140ERSuffix.tailWord,Raw140ERSuffix.rho,Nat.add_zero,List.append_assoc] using Reach.trans (⟨_,h0⟩ : Reach base _ _) h1
  | t1155 =>
    have h0 := Raw140ERSuffixLocal.prep1155 (AB (n+1) ++ X)
    have h1 := exitFront 2 n X [S 5,S 1,S 1]
    simp only [U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h1
    simpa only [Raw14042Bank.extra,aword,an,Raw140ERSuffix.tailWord,Raw140ERSuffix.rho,List.nil_append,Raw140ERSuffix.tailWord,Raw140ERSuffix.rho,Nat.add_zero,List.append_assoc] using Reach.trans (⟨_,h0⟩ : Reach base _ _) h1
  | t11511 =>
    have h0 := Raw140ERSuffixLocal.prep11511 (AB (n+1) ++ X)
    have h1 := exitFront 2 n X [S 5,S 5,S 4,S 2]
    simp only [U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h1
    simpa only [Raw14042Bank.extra,aword,an,Raw140ERSuffix.tailWord,Raw140ERSuffix.rho,List.nil_append,Raw140ERSuffix.tailWord,Raw140ERSuffix.rho,Raw14042Bank.trip_snoc,List.append_assoc,List.cons_append,List.nil_append] using
      Reach.trans (⟨_,h0⟩ : Reach base _ _) h1


def aCfg (p n : Nat) (s : ATail) : Prim := boundary 0 true (U 3 p ++ [S 2]) (TA n ++ aword s)
def bSeedCfg (k u v : Nat) (s : ATail) : Prim :=
    boundary 4 true (S 1::(AB u ++ U 3 v ++ U 5 k)) (aword s)

theorem onePumpAll (p j b : Nat) (Y : List Sym) :
    Reach base (boundary 0 true (U 3 p ++ [S 2]) (S 0::(U 1 (2*j+b) ++ Y)))
      (boundary 0 true (U 3 (p+4*j) ++ [S 2]) (S 0::(U 1 b ++ Y))) := by
  induction j generalizing p with
  | zero => simpa only [Nat.mul_zero,Nat.zero_add,Nat.add_zero] using Reach.refl base _
  | succ j ih =>
    have h0 : Reach base (boundary 0 true (U 3 p ++ [S 2]) (S 0::(U 1 (2*(j+1)+b) ++ Y)))
        (boundary 0 true (U 3 (p+4) ++ [S 2]) (S 0::(U 1 (2*j+b) ++ Y))) := by
      simpa only [Mbase,show 2*(j+1)+b=(2*j+b)+1+1 by omega,
        U,List.replicate_succ,List.cons_append,List.append_assoc] using
          (show Reach base _ _ from ⟨_,oddPump p (U 1 (2*j+b) ++ Y)⟩)
    simpa only [show p+4+4*j=p+4*(j+1) by omega] using Reach.trans h0 (ih (p+4))

theorem oddHomogeneous (p : Nat) (Y : List Sym) (ho : p%2=1) :
    Reach base (boundary 4 true (U 3 (p+2)) (S 1::Y))
      (boundary 0 true (U 3 (2*p+6) ++ [S 2]) Y) := by
  have h0 : Reach base (boundary 4 true (U 3 (p+2)) (S 1::Y))
      (boundary 4 true [S 2] (U 1 (p+2) ++ S 5::Y)) := by
    simpa only [Mbase,show p+1+1=p+2 by omega] using
      (show Reach base _ _ from ⟨_,oddInit (p+1) Y⟩)
  have h1 : Reach base (boundary 4 true [S 2] (U 1 (p+2) ++ S 5::Y))
      (boundary 0 true (U 3 3 ++ [S 2]) (S 0::(U 1 p ++ S 5::Y))) := by
    simpa only [Mbase,show p+2=p+1+1 by omega,U,List.replicate_succ,List.replicate_zero,
      List.cons_append,List.nil_append] using (show Reach base _ _ from ⟨_,oddStart (U 1 p ++ S 5::Y)⟩)
  let j := (p-1)/2
  have hj : 2*j+1=p := by dsimp [j]; omega
  have hm : 3+4*j=2*p+1 := by omega
  have h2 : Reach base (boundary 0 true (U 3 3 ++ [S 2]) (S 0::(U 1 p ++ S 5::Y)))
      (boundary 0 true (U 3 (2*p+1) ++ [S 2]) (S 0::S 1::S 5::Y)) := by
    simpa only [hj,hm,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append] using onePumpAll 3 j 1 (S 5::Y)
  have h3 : Reach base (boundary 0 true (U 3 (2*p+1) ++ [S 2]) (S 0::S 1::S 5::Y))
      (boundary 0 true (U 3 (2*p+6) ++ [S 2]) Y) := by
    simpa only [Mbase,show 2*p+1+5=2*p+6 by omega] using
      (show Reach base _ _ from ⟨_,oddFinish (2*p+1) Y⟩)
  exact Reach.trans (Reach.trans h0 h1) (Reach.trans h2 h3)

theorem oddReturn (k u v : Nat) (s : ATail) (ho : (k+v+1)%2=1) (hu : 1≤u+(k+arank s)/6) :
    ∃ t : ATail, arank t=(k+arank s+1)%6 ∧
      R (bSeedCfg k u v s) (aCfg (2*(k+v+1)+6) (u+(k+arank s+1)/6-1) t) := by
  let n := (aTurn k s).1
  let r := (aTurn k s).2
  let z := u+n+ac r-1
  let t := an r
  have hbal := aTurn_balance k s
  have hlt := arank_lt r
  have hlt' := arank_lt t
  have hb := abalance r
  have hn : n=(k+arank s)/6 := by dsimp [n,r] at *; omega
  have hun : 1≤u+n := by omega
  have hbal' : 6*(n+ac r)+arank t=k+arank s+1 := by dsimp [n,r,t] at *; omega
  have hz : z=u+(k+arank s+1)/6-1 := by dsimp [z]; omega
  have hr : arank t=(k+arank s+1)%6 := by omega
  have h0 := bankIter k u v [] s
  have h0' : Reach base (bSeedCfg k u v s)
      (boundary 4 true (S 1::(AB (u+n) ++ U 3 (v+k))) (aword r)) := by
    simpa only [bSeedCfg,n,r,List.append_nil,List.append_assoc] using h0
  have h1 := exitAny (u+n-1) (U 3 (v+k)) r
  have h1' : Reach base (boundary 4 true (S 1::(AB (u+n) ++ U 3 (v+k))) (aword r))
      (boundary 4 true (U 3 (k+v+1+2)) (S 1::(TA z ++ aword t))) := by
    simpa only [show u+n-1+1=u+n by omega,show u+n-1+ac r=z by dsimp [z]; omega,
      show k+v+1+2=(v+k)+1+1+1 by omega,t,U,List.replicate_succ,List.cons_append] using h1
  have h2 := oddHomogeneous (k+v+1) (TA z ++ aword t) ho
  exact ⟨t,hr,by simpa only [aCfg,hz] using Reach.ext (M := M42) (fill_extends _ _) (Reach.trans (Reach.trans h0' h1') h2)⟩
#print axioms oddReturn
end Raw14042BGeneral
