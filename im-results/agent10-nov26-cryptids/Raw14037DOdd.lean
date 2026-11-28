import Raw14037DRoutes
namespace Raw14037DOdd
open BB6BlockFAR Raw140Orbit Raw140Extra Raw14037DTerm
open Raw140Double (Reach)
open Raw140ERSuffix Raw140ERExit Raw140ERSuffixLocal
set_option maxRecDepth 100000
set_option maxHeartbeats 0
attribute [local irreducible] boundary run

theorem drop1 (a : Nat) (X Y : List Sym) :
    Reach base (boundary 3 false (S 6::X) (U 4 (a+1) ++ S 2::S 1::Y))
      (boundary 3 false X (U 4 (a+2) ++ S 0::S 5::Y)) := by
  have h0 := frontAny a X (S 2::S 1::Y)
  have h1 := Raw140Framed.execute_sound base true true 9 27
    ⟨4,true,[S 0],[S 2,S 1]⟩ ⟨3,false,[S 5],[S 0,S 5]⟩ (U 5 (a+1) ++ X) Y (by decide +kernel)
  have h2 := sweepL base 3 (S 5) (S 4) 3 (a+2) X (S 0::S 5::Y) (by rfl)
  simp only [Raw140Framed.prim,List.cons_append,List.nil_append,ite_true] at h1
  have h1' : Reach base (boundary 4 true (S 0::(U 5 (a+1) ++ X)) (S 2::S 1::Y))
      (boundary 3 false (U 5 (a+2) ++ X) (S 0::S 5::Y)) := by
    exact ⟨_,h1⟩
  exact Reach.trans (Reach.trans h0 h1') ⟨_,h2⟩

theorem seed (X Y : List Sym) :
    run base 30 (boundary 4 true (S 0::X) (S 0::S 5::Y)) =
      some (boundary 4 true (S 1::S 2::S 5::X) Y) := by
  exact Raw140Framed.execute_sound base true true 10 30
    ⟨4,true,[S 0],[S 0,S 5]⟩ ⟨4,true,[S 1,S 2,S 5],[]⟩ X Y (by decide +kernel)

theorem pumpAny (n : Nat) (X Y : List Sym) :
    run base (21*n) (boundary 4 true (S 3::S 3::S 3::(trip133 n ++ X)) (S 1::Y)) =
    some (boundary 4 true (S 3::S 3::S 3::X) (S 1::(trip115 n ++ Y))) := by
  induction n generalizing Y with
  | zero => simp [trip133,trip115,run]
  | succ n ih =>
    have h0 := tripLoop (trip133 n ++ X) Y
    have h1 := ih (S 1::S 1::S 5::Y)
    simpa only [trip133,trip115_snoc,List.cons_append,List.append_assoc,List.nil_append,
      show (7+3*3+3+1+1)+21*n=21*(n+1) by omega] using join h0 h1

theorem finish (m : Nat) (X Y : List Sym) :
    Reach base (boundary 4 false (U 3 m ++ S 2::S 5::X) Y)
      (boundary 3 false X (S 2::(U 1 (m+1) ++ Y))) := by
  have h0 := sweepL base 4 (S 3) (S 1) 3 m (S 2::S 5::X) Y (by rfl)
  have h1 := Raw140Framed.execute_sound base true true 2 6
    ⟨4,false,[S 2,S 5],[]⟩ ⟨3,false,[],[S 2,S 1]⟩ X (U 1 m ++ Y) (by decide +kernel)
  exact ⟨_,join h0 h1⟩

theorem returnPrep (j n m : Nat) (X Y : List Sym) :
    Reach base (boundary 4 false (U 3 (j+1) ++ trip133 n ++ U 3 m ++ S 2::S 5::X) Y)
      (boundary 3 false X (S 2::(U 1 (m+2) ++ trip115 n ++ U 1 j ++ Y))) := by
  cases n with
  | zero =>
    simp only [trip133,trip115,List.nil_append,List.append_nil,List.append_assoc,merge]
    have h := finish (j+1+m) X Y
    rw [show j+1+m+1=m+2+j by omega] at h
    simpa only [merge] using h
  | succ n =>
    let Z := U 3 m ++ S 2::S 5::X
    have h0 := prepareCarry j (S 3::S 3::(trip133 n ++ Z)) Y
    have h1 := pumpAny n Z (U 1 j ++ Y)
    have h2 := stepR base 4 4 false (S 1) (S 5) 7 (S 3::S 3::S 3::Z) (trip115 n ++ U 1 j ++ Y) (by rfl)
    have h3 := finish (m+3) X (S 5::(trip115 n ++ U 1 j ++ Y))
    have h3' : Reach base (boundary 4 false (S 3::S 3::S 3::Z) (S 5::(trip115 n ++ U 1 j ++ Y)))
        (boundary 3 false X (S 2::(U 1 (m+2) ++ trip115 (n+1) ++ U 1 j ++ Y))) := by
      simp only [Z,trip115,U,List.replicate_succ,List.cons_append,List.append_assoc,rep_cons] at h3 ⊢
      exact h3
    simp only [U,List.replicate_succ,List.cons_append,trip133,List.append_assoc, Z, Bool.false_eq_true,ite_false,ite_true] at h0 h1 h2 h3'
    have h := Reach.trans (Reach.trans (Reach.trans ⟨_,h0⟩ ⟨_,h1⟩) ⟨_,h2⟩) h3'
    simpa only [U,List.replicate_succ,List.cons_append,trip133,List.append_assoc,Z] using h

theorem rotate (n m : Nat) (s : Tail) (X : List Sym) :
    Reach base (boundary 4 true (S 1::(trip133 n ++ U 3 m ++ S 2::S 5::X)) (tailWord s))
      (boundary 3 false X (S 2::(U 1 (m+2) ++ trip115 (n+extra s) ++ tailWord (rho s)))) := by
  let Z := trip133 n ++ U 3 m ++ S 2::S 5::X
  cases s with
  | t542 =>
    have h0 := prep542 Z
    have h1 := returnPrep 1 n m X [S 5,S 2]
    simp only [Z,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h0 h1
    simpa only [extra,rho,tailWord,Nat.add_zero,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] using Reach.trans ⟨_,h0⟩ h1
  | t152 =>
    have h0 := prep152 Z
    have h1 := returnPrep 1 n m X [S 1,S 2,S 1]
    simp only [Z,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h0 h1
    simpa only [extra,rho,tailWord,Nat.add_zero,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] using Reach.trans ⟨_,h0⟩ h1
  | t1121 =>
    have h0 := prep1121 Z
    have h1 := returnPrep 0 n m X [S 5,S 2,S 1,S 5]
    simp only [Z,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h0 h1
    simpa only [extra,rho,tailWord,Nat.add_zero,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] using Reach.trans ⟨_,h0⟩ h1
  | t5215 =>
    have h0 := prep5215 Z
    have h1 := returnPrep 0 n m X [S 1,S 1,S 5,S 5]
    simp only [Z,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h0 h1
    simpa only [extra,rho,tailWord,Nat.add_zero,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] using Reach.trans ⟨_,h0⟩ h1
  | t1155 =>
    have h0 := prep1155 Z
    have h1 := returnPrep 2 n m X [S 5,S 1,S 1]
    simp only [Z,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] at h0 h1
    simpa only [extra,rho,tailWord,Nat.add_zero,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] using Reach.trans ⟨_,h0⟩ h1
  | t11511 =>
    have h := Reach.trans ⟨_,prep11511 Z⟩ (returnPrep 2 n m X [S 5,S 5,S 4,S 2])
    simpa only [Z,extra,rho,tailWord,trip115_snoc,U,List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,List.append_assoc] using h

theorem rotateFront (n m : Nat) (s : Tail) (X : List Sym) :
    Reach base (boundary 4 true (S 0::X) (S 0::S 5::(U 1 m ++ trip115 n ++ tailWord s)))
      (boundary 3 false X (S 2::(U 1 (m+2) ++ trip115 (n+extra s) ++ tailWord (rho s)))) := by
  have h0 := seed X (U 1 m ++ trip115 n ++ tailWord s)
  have h1 := Raw140ERSweep.many m (S 2::S 5::X) (trip115 n ++ tailWord s)
  have h2 := Raw14037SixBank.erMany n (U 3 m ++ S 2::S 5::X) (tailWord s)
  have h3 := rotate n m s X
  simp only [List.append_assoc] at h0 h1 h2 h3 ⊢
  exact Reach.trans (Reach.trans (Reach.trans ⟨_,h0⟩ ⟨_,h1⟩) ⟨_,h2⟩) h3

theorem advance (a n m : Nat) (s : Tail) (X : List Sym) :
    Reach base (boundary 3 false (S 6::S 6::X) (U 4 (a+1) ++ S 2::(U 1 (m+1) ++ trip115 n ++ tailWord s)))
      (boundary 3 false X (U 4 (a+2) ++ S 2::(U 1 (m+2) ++ trip115 (n+extra s) ++ tailWord (rho s)))) := by
  have h0 := drop1 a (S 6::X) (U 1 m ++ trip115 n ++ tailWord s)
  have h1 := frontAny (a+1) X (S 0::S 5::(U 1 m ++ trip115 n ++ tailWord s))
  have h2 := rotateFront n m s (U 5 (a+2) ++ X)
  have h3 := sweepL base 3 (S 5) (S 4) 3 (a+2) X (S 2::(U 1 (m+2) ++ trip115 (n+extra s) ++ tailWord (rho s))) (by rfl)
  exact Reach.trans (Reach.trans (Reach.trans h0 h1) h2) ⟨_,h3⟩

def turn : Nat → Tail → Nat × Tail
  | 0,s => (0,s)
  | k+1,s => (extra s+(turn k (rho s)).1,(turn k (rho s)).2)

def J (a m n : Nat) (s : Tail) (X : List Sym) : Prim :=
  boundary 3 false X (U 4 a ++ S 2::(U 1 m ++ trip115 n ++ tailWord s))

theorem iterate (k a m n : Nat) (s : Tail) (X : List Sym) :
    Reach base (J (a+1) (m+1) n s (U 6 (2*k) ++ X))
      (J (a+1+k) (m+1+k) (n+(turn k s).1) (turn k s).2 X) := by
  induction k generalizing a m n s with
  | zero => simpa [U,turn,J] using Reach.refl base (J (a+1) (m+1) n s X)
  | succ k ih =>
    have h0 := advance a n m s (U 6 (2*k) ++ X)
    have h1 := ih (a+1) (m+1) (n+extra s) (rho s)
    simp only [J,show (a+1)+1=a+2 by omega,show (m+1)+1=m+2 by omega] at h1
    have h := Reach.trans h0 h1
    simpa only [J,turn,show 2*(k+1)=2*k+2 by omega,U,List.replicate_succ,List.cons_append,
      show a+2+k=a+1+(k+1) by omega,show m+2+k=m+1+(k+1) by omega,Nat.add_assoc] using h

theorem oddSeed (a : Nat) (X : List Sym) :
    Reach base (boundary 3 false (U 6 4 ++ X) (U 4 (a+1) ++ [S 2,S 1,S 5]))
      (J (a+3) 3 0 .t542 X) := by
  let r0 : Rule := ⟨[S 2,S 1,S 5],1,0,[S 0,S 5,S 5],9,27⟩
  let r1 : Rule := ⟨[S 0,S 5,S 5],0,0,[S 2,S 1,S 1,S 1,S 1],22,66⟩
  let r2 : Rule := ⟨[S 2,S 1,S 1,S 1,S 1],1,0,[S 0,S 5,S 1,S 1,S 1],9,27⟩
  let r3 : Rule := ⟨[S 0,S 5,S 1,S 1,S 1],0,0,[S 2,S 1,S 1,S 1,S 5,S 4,S 2],34,110⟩
  have h0 := r0.sound (by decide +kernel) a (S 6::S 6::S 6::X)
  have h1 := r1.sound (by decide +kernel) (a+1) (S 6::S 6::X)
  have h2 := r2.sound (by decide +kernel) (a+1) (S 6::X)
  have h3 := r3.sound (by decide +kernel) (a+2) X
  simp only [r0,r1,r2,r3,Rule.src,Rule.extra5,Rule.extra4,Rule.dst,Nat.add_zero] at h0 h1 h2 h3
  exact Reach.trans (Reach.trans (Reach.trans h0 h1) h2) h3

#print axioms advance
#print axioms iterate
#print axioms oddSeed
end Raw14037DOdd
