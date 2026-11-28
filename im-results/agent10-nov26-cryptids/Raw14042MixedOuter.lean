import Raw14042Counter
namespace Raw14042MixedOuter
open BB6BlockFAR Raw140Orbit Raw140Extra Raw140Double
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [local irreducible] run boundary
private theorem rr {k : Nat} {c d : Prim} (h : run base k c = some d) : Reach base c d := ⟨k,h⟩

-- The complete framed boundary conversion after the even mixed counter.
-- All scanned rows belong to the common partial table.
theorem a224_to6 (p : Nat) (Y : List Sym) :
    Reach base (boundary 0 true (U 3 p ++ [S 2]) (S 2::S 2::S 4::S 6::Y))
      (boundary 0 true (U 3 (p+5) ++ [S 2]) (S 6::Y)) := by
  have h0 := rr (stepR base 0 4 false (S 2) (S 1) 3 (U 3 p ++ [S 2]) (S 2::S 4::S 6::Y) (by rfl))
  have h1 := rr (sweepL base 4 (S 3) (S 1) 3 p [S 2] (S 1::S 2::S 4::S 6::Y) (by rfl))
  have h2 := rr (stepL base 4 1 false (S 2) (S 1) 3 [] (U 1 (p+1) ++ S 2::S 4::S 6::Y) (by rfl))
  have h3 := rr (stepL base 1 2 true (S 0) (S 4) 1 [] (U 1 (p+2) ++ S 2::S 4::S 6::Y) (by rfl))
  have h4 := rr (sweepR base 2 (S 1) (S 6) 3 (p+2) [S 4] (S 2::S 4::S 6::Y) (by rfl))
  have h5 := rr (stepR base 2 3 true (S 2) (S 6) 7 (U 6 (p+2) ++ [S 4]) (S 4::S 6::Y) (by rfl))
  have h6 := rr (stepR base 3 1 false (S 4) (S 5) 1 (U 6 (p+3) ++ [S 4]) (S 6::Y) (by rfl))
  have h7 := rr (sweepL base 1 (S 6) (S 2) 3 (p+3) [S 4] (S 5::S 6::Y) (by rfl))
  have h8 := rr (stepL base 1 1 true (S 4) (S 5) 5 [] (U 2 (p+3) ++ S 5::S 6::Y) (by rfl))
  have h9 := rr (sweepR base 1 (S 2) (S 5) 3 (p+3) [S 5] (S 5::S 6::Y) (by rfl))
  have h10 := rr (stepR base 1 3 false (S 5) (S 4) 1 (U 5 (p+4)) (S 6::Y) (by rfl))
  have h11 := rr (sweepL base 3 (S 5) (S 4) 3 (p+4) [] (S 4::S 6::Y) (by rfl))
  have h12 := rr (stepL base 3 0 true (S 0) (S 2) 3 [] (U 4 (p+5) ++ S 6::Y) (by rfl))
  have h13 := rr (sweepR base 0 (S 4) (S 3) 3 (p+5) [S 2] (S 6::Y) (by rfl))
  simp only [ite_true,ite_false,Bool.false_eq_true,Szero,left_zero] at h0 h2 h3 h5 h6 h8 h10 h12
  have g1 : Reach base (boundary 0 true (U 3 p ++ [S 2]) (S 2::S 2::S 4::S 6::Y))
      (boundary 1 false [] (U 1 (p+2) ++ S 2::S 4::S 6::Y)) := by
    apply Reach.trans h0
    apply Reach.trans h1
    simpa only [U,List.replicate_succ,List.cons_append,rep_cons] using h2
  have g2 := Reach.trans (Reach.trans g1 h3) h4
  have g3 := Reach.trans (Reach.trans g2 h5) h6
  have g4 := Reach.trans (Reach.trans (Reach.trans g3 h7) h8) h9
  have g5 : Reach base (boundary 0 true (U 3 p ++ [S 2]) (S 2::S 2::S 4::S 6::Y))
      (boundary 3 false [] (U 4 (p+5) ++ S 6::Y)) := by
    have g4' : Reach base (boundary 0 true (U 3 p ++ [S 2]) (S 2::S 2::S 4::S 6::Y))
        (boundary 1 true (U 5 (p+4)) (S 5::S 6::Y)) := by
      simpa only [U,List.replicate_succ'] using g4
    have h11' : Reach base (boundary 3 false (U 5 (p+4)) (S 4::S 6::Y))
        (boundary 3 false [] (U 4 (p+5) ++ S 6::Y)) := by
      simpa only [U,List.replicate_succ,List.cons_append,rep_cons,List.append_nil] using h11
    exact Reach.trans (Reach.trans g4' h10) h11'
  exact Reach.trans (Reach.trans g5 h12) h13

-- Iteration of the established two-symbol pump.  The retained final 2
-- is an actual marker, so the untouched suffix can begin with any block.
theorem twosIter (k p : Nat) (Y : List Sym) :
    Reach base (boundary 0 true (U 3 p ++ [S 2]) (U 2 (2*k) ++ S 2::Y))
      (boundary 0 true (U 3 (p+4*k) ++ [S 2]) (S 2::Y)) := by
  induction k generalizing p with
  | zero => simpa using Reach.refl base (boundary 0 true (U 3 p ++ [S 2]) (S 2::Y))
  | succ k ih =>
    have h0 := rr (Raw14042CounterLocal.twoPump p (U 2 (2*k) ++ Y))
    have h1 := ih (p+4)
    have hh : Reach base (boundary 0 true (U 3 p ++ [S 2]) (U 2 (2*(k+1)) ++ S 2::Y))
        (boundary 0 true (U 3 (p+4) ++ [S 2]) (U 2 (2*k) ++ S 2::Y)) := by
      simpa only [U,show 2*(k+1)=2*k+2 by omega,List.replicate_succ,List.cons_append,rep_cons] using h0
    simpa only [show p+4+4*k=p+4*(k+1) by omega] using Reach.trans hh h1

theorem initDrain (k : Nat) (Y : List Sym) :
    Reach base (boundary 1 false [] (U 2 (2*k+2) ++ Y))
      (boundary 0 true (U 3 (4*k+2) ++ [S 2]) (S 2::Y)) := by
  have h0 := rr (Raw14042CounterLocal.initTwos (U 2 (2*k) ++ Y))
  have h1 := twosIter k 2 Y
  have hh : Reach base (boundary 1 false [] (U 2 (2*k+2) ++ Y))
      (boundary 0 true (U 3 2 ++ [S 2]) (U 2 (2*k) ++ S 2::Y)) := by
    simpa only [U,List.replicate_succ,List.replicate_zero,List.cons_append,rep_cons,List.nil_append] using h0
  simpa only [show 2+4*k=4*k+2 by omega] using Reach.trans hh h1

#print axioms a224_to6
#print axioms twosIter
#print axioms initDrain
end Raw14042MixedOuter
