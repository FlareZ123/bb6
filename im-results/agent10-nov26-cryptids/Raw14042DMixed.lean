import Raw14042AWord
import Raw140DoubleLocal
namespace Raw14042DMixed
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double Raw14042AWord
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
attribute [local irreducible] boundary run
abbrev AT := Raw140ERSuffix.Tail
abbrev aw := Raw140ERSuffix.tailWord
abbrev an := Raw140ERSuffix.rho

theorem fourScan (a : Nat) (X Y : List Sym) : 
    Reach base (boundary 2 true (S 4::X) (U 4 (a+1) ++ Y))
      (boundary 2 true (S 4::(U 5 a ++ X)) (S 4::Y)) := by
  induction a generalizing X with
  | zero => exact Reach.refl base _
  | succ a ih =>
    have h0 := forward4_4 X (U 4 a ++ Y)
    have h1 := ih (S 5::X)
    simpa only [U,List.replicate_succ,List.cons_append,rep_cons] using Reach.trans ⟨_,h0⟩ h1

theorem phase1 (a b : Nat) (X Y : List Sym) :
    Reach base (boundary 3 false (S 6::X) (U 4 (a+1) ++ S 2::(U 1 (b+1) ++ Y)))
      (boundary 3 false X (U 4 (a+2) ++ S 0::S 5::(U 1 b ++ Y))) := by
  have h0 := lift_4 X (U 4 a ++ S 2::(U 1 (b+1) ++ Y))
  have h1 := fourScan a X (S 2::(U 1 (b+1) ++ Y))
  have h2 := Raw14042AWordLocal.first (U 5 a ++ X) (U 1 b ++ Y)
  have h3 := sweepL base 3 (S 5) (S 4) 3 (a+2) X (S 0::S 5::(U 1 b ++ Y)) (by rfl)
  exact Reach.trans (Reach.trans (Reach.trans ⟨_,h0⟩ h1) ⟨_,h2⟩) ⟨_,h3⟩

theorem phase2 (a : Nat) (X : List Sym) (W : List Bool) (s : AT) :
    Reach base (boundary 3 false (S 6::X) (U 4 (a+1) ++ S 0::S 5::(w15 W ++ aw s)))
      (boundary 3 false X (U 4 (a+1) ++ S 2::S 1::S 1::(w15 W ++ TA (ac s) ++ aw (an s)))) := by
  have h0 := lift_4 X (U 4 a ++ S 0::S 5::(w15 W ++ aw s))
  have h1 := fourScan a X (S 0::S 5::(w15 W ++ aw s))
  have h2 := mixTail W (U 5 a ++ X) s
  have h3 := sweepL base 3 (S 5) (S 4) 3 (a+1) X (S 2::S 1::S 1::(w15 W ++ TA (ac s) ++ aw (an s))) (by rfl)
  exact Reach.trans (Reach.trans (Reach.trans ⟨_,h0⟩ h1) h2) ⟨_,h3⟩

def P (a b : Nat) (X : List Sym) (W : List Bool) (s : AT) : Prim :=
  boundary 3 false X (U 4 (a+1) ++ S 2::(U 1 (b+1) ++ S 5::(w15 W ++ aw s)))

theorem pair (a b : Nat) (X : List Sym) (W : List Bool) (s : AT) :
    Reach base (P a b (S 6::S 6::X) W s)
      (P (a+1) (b+1) X (W ++ tr15 (ac s)) (an s)) := by
  have h0 := phase1 a b (S 6::X) (S 5::(w15 W ++ aw s))
  have h1 := phase2 (a+1) X (List.replicate b false ++ true::W) s
  have h1' : Reach base
      (boundary 3 false (S 6::X) (U 4 (a+2) ++ S 0::S 5::(U 1 b ++ S 5::(w15 W ++ aw s))))
      (P (a+1) (b+1) X (W ++ tr15 (ac s)) (an s)) := by
    simpa only [P,w15_append,w15_one,w15_tr,w15,ite_true,U,List.replicate_succ,List.cons_append,List.append_assoc] using h1
  exact Reach.trans h0 h1'

def turn : Nat → AT → Nat × AT
  | 0,s => (0,s)
  | k+1,s => (ac s+(turn k (an s)).1,(turn k (an s)).2)

theorem tr15_add (m n : Nat) : tr15 (m+n) = tr15 m ++ tr15 n := by
  induction m with
  | zero => simp [tr15]
  | succ m ih => simp [Nat.succ_add,tr15,ih]

theorem pairs (k a b : Nat) (X : List Sym) (W : List Bool) (s : AT) :
    Reach base (P a b (U 6 (2*k) ++ X) W s)
      (P (a+k) (b+k) X (W ++ tr15 (turn k s).1) (turn k s).2) := by
  induction k generalizing a b W s with
  | zero => simpa [U,turn,tr15] using Reach.refl base (P a b X W s)
  | succ k ih =>
    have h0 := pair a b (U 6 (2*k) ++ X) W s
    have h1 := ih (a+1) (b+1) (W ++ tr15 (ac s)) (an s)
    simpa only [U,List.replicate_succ,List.cons_append,turn,← tr15_add,List.append_assoc,
      show 2*(k+1)=2*k+2 by omega,show a+1+k=a+(k+1) by omega,show b+1+k=b+(k+1) by omega] using Reach.trans h0 h1
#print axioms pair
#print axioms pairs
end Raw14042DMixed
