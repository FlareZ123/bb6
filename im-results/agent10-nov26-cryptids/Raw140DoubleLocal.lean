import Raw140ExtraCore
namespace Raw140Double
open BB6BlockFAR Raw140Orbit Raw140Extra
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def M4 : Table := fill (some ⟨true,true,5⟩) (some ⟨false,false,1⟩)
def M13 : Table := fill (some ⟨true,true,5⟩) (some ⟨false,true,3⟩)
theorem forward4_4 (X : List Sym) (Y : List Sym) : run base (3+7+1+1+5+1+1) (boundary 2 true (S 4 :: X) (S 4 :: S 4 :: Y)) = some (boundary 2 true (S 4 :: (S 5 :: X)) (S 4 :: Y)) := by
  have h0 : run base 3 (boundary 2 true (S 4 :: X) (S 4 :: S 4 :: Y)) = some (boundary 3 false (S 4 :: X) (S 6 :: (S 4 :: Y))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 3 false (S 4) (S 6) 3 (S 4 :: X) (S 4 :: Y) (by rfl)
  have h1 : run base 7 (boundary 3 false (S 4 :: X) (S 6 :: (S 4 :: Y))) = some (boundary 4 true (S 1 :: X) (S 6 :: (S 4 :: Y))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 4 true (S 4) (S 1) 7 X (S 6 :: (S 4 :: Y)) (by rfl)
  have h2 : run base 1 (boundary 4 true (S 1 :: X) (S 6 :: (S 4 :: Y))) = some (boundary 1 false (S 1 :: X) (S 6 :: (S 4 :: Y))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 6) (S 6) 1 (S 1 :: X) (S 4 :: Y) (by rfl)
  have h3 : run base 1 (boundary 1 false (S 1 :: X) (S 6 :: (S 4 :: Y))) = some (boundary 2 true (S 5 :: X) (S 6 :: (S 4 :: Y))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 1) (S 5) 1 X (S 6 :: (S 4 :: Y)) (by rfl)
  have h4 : run base 5 (boundary 2 true (S 5 :: X) (S 6 :: (S 4 :: Y))) = some (boundary 4 true (S 0 :: (S 5 :: X)) (S 4 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 4 true (S 6) (S 0) 5 (S 5 :: X) (S 4 :: Y) (by rfl)
  have h5 : run base 1 (boundary 4 true (S 0 :: (S 5 :: X)) (S 4 :: Y)) = some (boundary 1 false (S 0 :: (S 5 :: X)) (S 4 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 4) (S 4) 1 (S 0 :: (S 5 :: X)) Y (by rfl)
  have h6 : run base 1 (boundary 1 false (S 0 :: (S 5 :: X)) (S 4 :: Y)) = some (boundary 2 true (S 4 :: (S 5 :: X)) (S 4 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 0) (S 4) 1 (S 5 :: X) (S 4 :: Y) (by rfl)
  exact (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6)

theorem forward6_4 (X : List Sym) (Y : List Sym) : run base (5+1+1) (boundary 2 true (S 4 :: X) (S 6 :: (S 4 :: Y))) = some (boundary 2 true (S 4 :: S 4 :: X) (S 4 :: Y)) := by
  have h0 : run base 5 (boundary 2 true (S 4 :: X) (S 6 :: (S 4 :: Y))) = some (boundary 4 true (S 0 :: (S 4 :: X)) (S 4 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 4 true (S 6) (S 0) 5 (S 4 :: X) (S 4 :: Y) (by rfl)
  have h1 : run base 1 (boundary 4 true (S 0 :: (S 4 :: X)) (S 4 :: Y)) = some (boundary 1 false (S 0 :: (S 4 :: X)) (S 4 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 4) (S 4) 1 (S 0 :: (S 4 :: X)) Y (by rfl)
  have h2 : run base 1 (boundary 1 false (S 0 :: (S 4 :: X)) (S 4 :: Y)) = some (boundary 2 true (S 4 :: S 4 :: X) (S 4 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 0) (S 4) 1 (S 4 :: X) (S 4 :: Y) (by rfl)
  exact (join (join h0 h1) h2)

theorem lift_4 (X : List Sym) (Y : List Sym) : run base (3+1+1) (boundary 3 false (S 6 :: X) (S 4 :: Y)) = some (boundary 2 true (S 4 :: X) (S 4 :: Y)) := by
  have h0 : run base 3 (boundary 3 false (S 6 :: X) (S 4 :: Y)) = some (boundary 4 true (S 0 :: X) (S 4 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 4 true (S 6) (S 0) 3 X (S 4 :: Y) (by rfl)
  have h1 : run base 1 (boundary 4 true (S 0 :: X) (S 4 :: Y)) = some (boundary 1 false (S 0 :: X) (S 4 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 4) (S 4) 1 (S 0 :: X) Y (by rfl)
  have h2 : run base 1 (boundary 1 false (S 0 :: X) (S 4 :: Y)) = some (boundary 2 true (S 4 :: X) (S 4 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 0) (S 4) 1 X (S 4 :: Y) (by rfl)
  exact (join (join h0 h1) h2)

theorem forward4_6 (X : List Sym) (Y : List Sym) : run base (3+7+1+1+5+1+1) (boundary 2 true (S 4 :: X) (S 4 :: (S 6 :: Y))) = some (boundary 2 true (S 4 :: (S 5 :: X)) (S 6 :: Y)) := by
  have h0 : run base 3 (boundary 2 true (S 4 :: X) (S 4 :: (S 6 :: Y))) = some (boundary 3 false (S 4 :: X) (S 6 :: S 6 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 3 false (S 4) (S 6) 3 (S 4 :: X) (S 6 :: Y) (by rfl)
  have h1 : run base 7 (boundary 3 false (S 4 :: X) (S 6 :: S 6 :: Y)) = some (boundary 4 true (S 1 :: X) (S 6 :: S 6 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 4 true (S 4) (S 1) 7 X (S 6 :: S 6 :: Y) (by rfl)
  have h2 : run base 1 (boundary 4 true (S 1 :: X) (S 6 :: S 6 :: Y)) = some (boundary 1 false (S 1 :: X) (S 6 :: S 6 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 6) (S 6) 1 (S 1 :: X) (S 6 :: Y) (by rfl)
  have h3 : run base 1 (boundary 1 false (S 1 :: X) (S 6 :: S 6 :: Y)) = some (boundary 2 true (S 5 :: X) (S 6 :: S 6 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 1) (S 5) 1 X (S 6 :: S 6 :: Y) (by rfl)
  have h4 : run base 5 (boundary 2 true (S 5 :: X) (S 6 :: S 6 :: Y)) = some (boundary 4 true (S 0 :: (S 5 :: X)) (S 6 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 4 true (S 6) (S 0) 5 (S 5 :: X) (S 6 :: Y) (by rfl)
  have h5 : run base 1 (boundary 4 true (S 0 :: (S 5 :: X)) (S 6 :: Y)) = some (boundary 1 false (S 0 :: (S 5 :: X)) (S 6 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 6) (S 6) 1 (S 0 :: (S 5 :: X)) Y (by rfl)
  have h6 : run base 1 (boundary 1 false (S 0 :: (S 5 :: X)) (S 6 :: Y)) = some (boundary 2 true (S 4 :: (S 5 :: X)) (S 6 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 0) (S 4) 1 (S 5 :: X) (S 6 :: Y) (by rfl)
  exact (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6)

theorem forward6_6 (X : List Sym) (Y : List Sym) : run base (5+1+1) (boundary 2 true (S 4 :: X) (S 6 :: S 6 :: Y)) = some (boundary 2 true (S 4 :: S 4 :: X) (S 6 :: Y)) := by
  have h0 : run base 5 (boundary 2 true (S 4 :: X) (S 6 :: S 6 :: Y)) = some (boundary 4 true (S 0 :: (S 4 :: X)) (S 6 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 4 true (S 6) (S 0) 5 (S 4 :: X) (S 6 :: Y) (by rfl)
  have h1 : run base 1 (boundary 4 true (S 0 :: (S 4 :: X)) (S 6 :: Y)) = some (boundary 1 false (S 0 :: (S 4 :: X)) (S 6 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 6) (S 6) 1 (S 0 :: (S 4 :: X)) Y (by rfl)
  have h2 : run base 1 (boundary 1 false (S 0 :: (S 4 :: X)) (S 6 :: Y)) = some (boundary 2 true (S 4 :: S 4 :: X) (S 6 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 0) (S 4) 1 (S 4 :: X) (S 6 :: Y) (by rfl)
  exact (join (join h0 h1) h2)

theorem lift_6 (X : List Sym) (Y : List Sym) : run base (3+1+1) (boundary 3 false (S 6 :: X) (S 6 :: Y)) = some (boundary 2 true (S 4 :: X) (S 6 :: Y)) := by
  have h0 : run base 3 (boundary 3 false (S 6 :: X) (S 6 :: Y)) = some (boundary 4 true (S 0 :: X) (S 6 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 4 true (S 6) (S 0) 3 X (S 6 :: Y) (by rfl)
  have h1 : run base 1 (boundary 4 true (S 0 :: X) (S 6 :: Y)) = some (boundary 1 false (S 0 :: X) (S 6 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 6) (S 6) 1 (S 0 :: X) Y (by rfl)
  have h2 : run base 1 (boundary 1 false (S 0 :: X) (S 6 :: Y)) = some (boundary 2 true (S 4 :: X) (S 6 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 0) (S 4) 1 X (S 6 :: Y) (by rfl)
  exact (join (join h0 h1) h2)

theorem reverse4 (X : List Sym) (Y : List Sym) : run base (3) (boundary 3 false (S 5 :: S 5 :: X) Y) = some (boundary 3 false (S 5 :: X) (S 4 :: Y)) := by
  have h0 : run base 3 (boundary 3 false (S 5 :: S 5 :: X) Y) = some (boundary 3 false (S 5 :: X) (S 4 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 3 false (S 5) (S 4) 3 (S 5 :: X) Y (by rfl)
  exact h0

theorem reverse6 (X : List Sym) (Y : List Sym) : run base (3+7+1+1+3) (boundary 3 false (S 5 :: (S 4 :: X)) Y) = some (boundary 3 false (S 5 :: X) (S 6 :: Y)) := by
  have h0 : run base 3 (boundary 3 false (S 5 :: (S 4 :: X)) Y) = some (boundary 3 false (S 4 :: X) (S 4 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 3 false (S 5) (S 4) 3 (S 4 :: X) Y (by rfl)
  have h1 : run base 7 (boundary 3 false (S 4 :: X) (S 4 :: Y)) = some (boundary 4 true (S 1 :: X) (S 4 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 4 true (S 4) (S 1) 7 X (S 4 :: Y) (by rfl)
  have h2 : run base 1 (boundary 4 true (S 1 :: X) (S 4 :: Y)) = some (boundary 1 false (S 1 :: X) (S 4 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 4) (S 4) 1 (S 1 :: X) Y (by rfl)
  have h3 : run base 1 (boundary 1 false (S 1 :: X) (S 4 :: Y)) = some (boundary 2 true (S 5 :: X) (S 4 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 1) (S 5) 1 X (S 4 :: Y) (by rfl)
  have h4 : run base 3 (boundary 2 true (S 5 :: X) (S 4 :: Y)) = some (boundary 3 false (S 5 :: X) (S 6 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 3 false (S 4) (S 6) 3 (S 5 :: X) Y (by rfl)
  exact (join (join (join (join h0 h1) h2) h3) h4)

theorem tail62 (X : List Sym) : run base (5+1+1+7+1+3+5+3+1+3+3+7+1+1+3) (boundary 2 true (S 4 :: X) (S 6 :: (S 2 :: []))) = some (boundary 3 false (S 5 :: X) (S 6 :: (S 4 :: []))) := by
  have h0 : run base 5 (boundary 2 true (S 4 :: X) (S 6 :: (S 2 :: []))) = some (boundary 4 true (S 0 :: (S 4 :: X)) (S 2 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 4 true (S 6) (S 0) 5 (S 4 :: X) (S 2 :: []) (by rfl)
  have h1 : run base 1 (boundary 4 true (S 0 :: (S 4 :: X)) (S 2 :: [])) = some (boundary 1 false (S 0 :: (S 4 :: X)) (S 2 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 2) (S 2) 1 (S 0 :: (S 4 :: X)) [] (by rfl)
  have h2 : run base 1 (boundary 1 false (S 0 :: (S 4 :: X)) (S 2 :: [])) = some (boundary 2 true (S 4 :: S 4 :: X) (S 2 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 0) (S 4) 1 (S 4 :: X) (S 2 :: []) (by rfl)
  have h3 : run base 7 (boundary 2 true (S 4 :: S 4 :: X) (S 2 :: [])) = some (boundary 3 true (S 6 :: (S 4 :: S 4 :: X)) []) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 3 true (S 2) (S 6) 7 (S 4 :: S 4 :: X) [] (by rfl)
  have h4 : run base 1 (boundary 3 true (S 6 :: (S 4 :: S 4 :: X)) []) = some (boundary 1 false (S 6 :: (S 4 :: S 4 :: X)) (S 1 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 3 1 false (S 0) (S 1) 1 (S 6 :: (S 4 :: S 4 :: X)) [] (by rfl)
  have h5 : run base 3 (boundary 1 false (S 6 :: (S 4 :: S 4 :: X)) (S 1 :: [])) = some (boundary 1 false (S 4 :: S 4 :: X) (S 2 :: (S 1 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 1 false (S 6) (S 2) 3 (S 4 :: S 4 :: X) (S 1 :: []) (by rfl)
  have h6 : run base 5 (boundary 1 false (S 4 :: S 4 :: X) (S 2 :: (S 1 :: []))) = some (boundary 1 true (S 5 :: (S 4 :: X)) (S 2 :: (S 1 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 1 true (S 4) (S 5) 5 (S 4 :: X) (S 2 :: (S 1 :: [])) (by rfl)
  have h7 : run base 3 (boundary 1 true (S 5 :: (S 4 :: X)) (S 2 :: (S 1 :: []))) = some (boundary 1 true (S 5 :: S 5 :: (S 4 :: X)) (S 1 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 1 1 true (S 2) (S 5) 3 (S 5 :: (S 4 :: X)) (S 1 :: []) (by rfl)
  have h8 : run base 1 (boundary 1 true (S 5 :: S 5 :: (S 4 :: X)) (S 1 :: [])) = some (boundary 3 false (S 5 :: S 5 :: (S 4 :: X)) []) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 1 3 false (S 1) (S 0) 1 (S 5 :: S 5 :: (S 4 :: X)) [] (by rfl)
  have h9 : run base 3 (boundary 3 false (S 5 :: S 5 :: (S 4 :: X)) []) = some (boundary 3 false (S 5 :: (S 4 :: X)) (S 4 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 3 false (S 5) (S 4) 3 (S 5 :: (S 4 :: X)) [] (by rfl)
  have h10 : run base 3 (boundary 3 false (S 5 :: (S 4 :: X)) (S 4 :: [])) = some (boundary 3 false (S 4 :: X) (S 4 :: S 4 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 3 false (S 5) (S 4) 3 (S 4 :: X) (S 4 :: []) (by rfl)
  have h11 : run base 7 (boundary 3 false (S 4 :: X) (S 4 :: S 4 :: [])) = some (boundary 4 true (S 1 :: X) (S 4 :: S 4 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 4 true (S 4) (S 1) 7 X (S 4 :: S 4 :: []) (by rfl)
  have h12 : run base 1 (boundary 4 true (S 1 :: X) (S 4 :: S 4 :: [])) = some (boundary 1 false (S 1 :: X) (S 4 :: S 4 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 4) (S 4) 1 (S 1 :: X) (S 4 :: []) (by rfl)
  have h13 : run base 1 (boundary 1 false (S 1 :: X) (S 4 :: S 4 :: [])) = some (boundary 2 true (S 5 :: X) (S 4 :: S 4 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 1) (S 5) 1 X (S 4 :: S 4 :: []) (by rfl)
  have h14 : run base 3 (boundary 2 true (S 5 :: X) (S 4 :: S 4 :: [])) = some (boundary 3 false (S 5 :: X) (S 6 :: (S 4 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 3 false (S 4) (S 6) 3 (S 5 :: X) (S 4 :: []) (by rfl)
  exact (join (join (join (join (join (join (join (join (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14)

theorem tail64 (X : List Sym) : run base (5+1+1+3+7+1+1+5+1+1+3+7+1+1+7+1+3+3+3+7+1+1+3) (boundary 2 true (S 4 :: X) (S 6 :: (S 4 :: []))) = some (boundary 3 false (S 5 :: X) (S 6 :: (S 2 :: S 2 :: (S 1 :: [])))) := by
  have h0 : run base 5 (boundary 2 true (S 4 :: X) (S 6 :: (S 4 :: []))) = some (boundary 4 true (S 0 :: (S 4 :: X)) (S 4 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 4 true (S 6) (S 0) 5 (S 4 :: X) (S 4 :: []) (by rfl)
  have h1 : run base 1 (boundary 4 true (S 0 :: (S 4 :: X)) (S 4 :: [])) = some (boundary 1 false (S 0 :: (S 4 :: X)) (S 4 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 4) (S 4) 1 (S 0 :: (S 4 :: X)) [] (by rfl)
  have h2 : run base 1 (boundary 1 false (S 0 :: (S 4 :: X)) (S 4 :: [])) = some (boundary 2 true (S 4 :: S 4 :: X) (S 4 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 0) (S 4) 1 (S 4 :: X) (S 4 :: []) (by rfl)
  have h3 : run base 3 (boundary 2 true (S 4 :: S 4 :: X) (S 4 :: [])) = some (boundary 3 false (S 4 :: S 4 :: X) (S 6 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 3 false (S 4) (S 6) 3 (S 4 :: S 4 :: X) [] (by rfl)
  have h4 : run base 7 (boundary 3 false (S 4 :: S 4 :: X) (S 6 :: [])) = some (boundary 4 true (S 1 :: (S 4 :: X)) (S 6 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 4 true (S 4) (S 1) 7 (S 4 :: X) (S 6 :: []) (by rfl)
  have h5 : run base 1 (boundary 4 true (S 1 :: (S 4 :: X)) (S 6 :: [])) = some (boundary 1 false (S 1 :: (S 4 :: X)) (S 6 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 6) (S 6) 1 (S 1 :: (S 4 :: X)) [] (by rfl)
  have h6 : run base 1 (boundary 1 false (S 1 :: (S 4 :: X)) (S 6 :: [])) = some (boundary 2 true (S 5 :: (S 4 :: X)) (S 6 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 1) (S 5) 1 (S 4 :: X) (S 6 :: []) (by rfl)
  have h7 : run base 5 (boundary 2 true (S 5 :: (S 4 :: X)) (S 6 :: [])) = some (boundary 4 true (S 0 :: (S 5 :: (S 4 :: X))) []) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 4 true (S 6) (S 0) 5 (S 5 :: (S 4 :: X)) [] (by rfl)
  have h8 : run base 1 (boundary 4 true (S 0 :: (S 5 :: (S 4 :: X))) []) = some (boundary 1 false (S 0 :: (S 5 :: (S 4 :: X))) []) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 0) (S 0) 1 (S 0 :: (S 5 :: (S 4 :: X))) [] (by rfl)
  have h9 : run base 1 (boundary 1 false (S 0 :: (S 5 :: (S 4 :: X))) []) = some (boundary 2 true (S 4 :: (S 5 :: (S 4 :: X))) []) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 0) (S 4) 1 (S 5 :: (S 4 :: X)) [] (by rfl)
  have h10 : run base 3 (boundary 2 true (S 4 :: (S 5 :: (S 4 :: X))) []) = some (boundary 3 false (S 4 :: (S 5 :: (S 4 :: X))) (S 2 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 3 false (S 0) (S 2) 3 (S 4 :: (S 5 :: (S 4 :: X))) [] (by rfl)
  have h11 : run base 7 (boundary 3 false (S 4 :: (S 5 :: (S 4 :: X))) (S 2 :: [])) = some (boundary 4 true (S 1 :: (S 5 :: (S 4 :: X))) (S 2 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 4 true (S 4) (S 1) 7 (S 5 :: (S 4 :: X)) (S 2 :: []) (by rfl)
  have h12 : run base 1 (boundary 4 true (S 1 :: (S 5 :: (S 4 :: X))) (S 2 :: [])) = some (boundary 1 false (S 1 :: (S 5 :: (S 4 :: X))) (S 2 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 2) (S 2) 1 (S 1 :: (S 5 :: (S 4 :: X))) [] (by rfl)
  have h13 : run base 1 (boundary 1 false (S 1 :: (S 5 :: (S 4 :: X))) (S 2 :: [])) = some (boundary 2 true (S 5 :: S 5 :: (S 4 :: X)) (S 2 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 1) (S 5) 1 (S 5 :: (S 4 :: X)) (S 2 :: []) (by rfl)
  have h14 : run base 7 (boundary 2 true (S 5 :: S 5 :: (S 4 :: X)) (S 2 :: [])) = some (boundary 3 true (S 6 :: (S 5 :: S 5 :: (S 4 :: X))) []) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 3 true (S 2) (S 6) 7 (S 5 :: S 5 :: (S 4 :: X)) [] (by rfl)
  have h15 : run base 1 (boundary 3 true (S 6 :: (S 5 :: S 5 :: (S 4 :: X))) []) = some (boundary 1 false (S 6 :: (S 5 :: S 5 :: (S 4 :: X))) (S 1 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 3 1 false (S 0) (S 1) 1 (S 6 :: (S 5 :: S 5 :: (S 4 :: X))) [] (by rfl)
  have h16 : run base 3 (boundary 1 false (S 6 :: (S 5 :: S 5 :: (S 4 :: X))) (S 1 :: [])) = some (boundary 1 false (S 5 :: S 5 :: (S 4 :: X)) (S 2 :: (S 1 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 1 false (S 6) (S 2) 3 (S 5 :: S 5 :: (S 4 :: X)) (S 1 :: []) (by rfl)
  have h17 : run base 3 (boundary 1 false (S 5 :: S 5 :: (S 4 :: X)) (S 2 :: (S 1 :: []))) = some (boundary 3 false (S 5 :: (S 4 :: X)) (S 2 :: S 2 :: (S 1 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 3 false (S 5) (S 2) 3 (S 5 :: (S 4 :: X)) (S 2 :: (S 1 :: [])) (by rfl)
  have h18 : run base 3 (boundary 3 false (S 5 :: (S 4 :: X)) (S 2 :: S 2 :: (S 1 :: []))) = some (boundary 3 false (S 4 :: X) (S 4 :: (S 2 :: S 2 :: (S 1 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 3 false (S 5) (S 4) 3 (S 4 :: X) (S 2 :: S 2 :: (S 1 :: [])) (by rfl)
  have h19 : run base 7 (boundary 3 false (S 4 :: X) (S 4 :: (S 2 :: S 2 :: (S 1 :: [])))) = some (boundary 4 true (S 1 :: X) (S 4 :: (S 2 :: S 2 :: (S 1 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 4 true (S 4) (S 1) 7 X (S 4 :: (S 2 :: S 2 :: (S 1 :: []))) (by rfl)
  have h20 : run base 1 (boundary 4 true (S 1 :: X) (S 4 :: (S 2 :: S 2 :: (S 1 :: [])))) = some (boundary 1 false (S 1 :: X) (S 4 :: (S 2 :: S 2 :: (S 1 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 4) (S 4) 1 (S 1 :: X) (S 2 :: S 2 :: (S 1 :: [])) (by rfl)
  have h21 : run base 1 (boundary 1 false (S 1 :: X) (S 4 :: (S 2 :: S 2 :: (S 1 :: [])))) = some (boundary 2 true (S 5 :: X) (S 4 :: (S 2 :: S 2 :: (S 1 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 1) (S 5) 1 X (S 4 :: (S 2 :: S 2 :: (S 1 :: []))) (by rfl)
  have h22 : run base 3 (boundary 2 true (S 5 :: X) (S 4 :: (S 2 :: S 2 :: (S 1 :: [])))) = some (boundary 3 false (S 5 :: X) (S 6 :: (S 2 :: S 2 :: (S 1 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 3 false (S 4) (S 6) 3 (S 5 :: X) (S 2 :: S 2 :: (S 1 :: [])) (by rfl)
  exact (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15) h16) h17) h18) h19) h20) h21) h22)

theorem tail6221 (X : List Sym) : run base (5+1+1+7+1+3+5+3+1+3+3+7+1+1+3) (boundary 2 true (S 4 :: X) (S 6 :: (S 2 :: S 2 :: (S 1 :: [])))) = some (boundary 3 false (S 5 :: X) (S 6 :: (S 4 :: (S 2 :: (S 1 :: []))))) := by
  have h0 : run base 5 (boundary 2 true (S 4 :: X) (S 6 :: (S 2 :: S 2 :: (S 1 :: [])))) = some (boundary 4 true (S 0 :: (S 4 :: X)) (S 2 :: S 2 :: (S 1 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 4 true (S 6) (S 0) 5 (S 4 :: X) (S 2 :: S 2 :: (S 1 :: [])) (by rfl)
  have h1 : run base 1 (boundary 4 true (S 0 :: (S 4 :: X)) (S 2 :: S 2 :: (S 1 :: []))) = some (boundary 1 false (S 0 :: (S 4 :: X)) (S 2 :: S 2 :: (S 1 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 2) (S 2) 1 (S 0 :: (S 4 :: X)) (S 2 :: (S 1 :: [])) (by rfl)
  have h2 : run base 1 (boundary 1 false (S 0 :: (S 4 :: X)) (S 2 :: S 2 :: (S 1 :: []))) = some (boundary 2 true (S 4 :: S 4 :: X) (S 2 :: S 2 :: (S 1 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 0) (S 4) 1 (S 4 :: X) (S 2 :: S 2 :: (S 1 :: [])) (by rfl)
  have h3 : run base 7 (boundary 2 true (S 4 :: S 4 :: X) (S 2 :: S 2 :: (S 1 :: []))) = some (boundary 3 true (S 6 :: (S 4 :: S 4 :: X)) (S 2 :: (S 1 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 3 true (S 2) (S 6) 7 (S 4 :: S 4 :: X) (S 2 :: (S 1 :: [])) (by rfl)
  have h4 : run base 1 (boundary 3 true (S 6 :: (S 4 :: S 4 :: X)) (S 2 :: (S 1 :: []))) = some (boundary 1 false (S 6 :: (S 4 :: S 4 :: X)) (S 3 :: (S 1 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 3 1 false (S 2) (S 3) 1 (S 6 :: (S 4 :: S 4 :: X)) (S 1 :: []) (by rfl)
  have h5 : run base 3 (boundary 1 false (S 6 :: (S 4 :: S 4 :: X)) (S 3 :: (S 1 :: []))) = some (boundary 1 false (S 4 :: S 4 :: X) (S 2 :: (S 3 :: (S 1 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 1 false (S 6) (S 2) 3 (S 4 :: S 4 :: X) (S 3 :: (S 1 :: [])) (by rfl)
  have h6 : run base 5 (boundary 1 false (S 4 :: S 4 :: X) (S 2 :: (S 3 :: (S 1 :: [])))) = some (boundary 1 true (S 5 :: (S 4 :: X)) (S 2 :: (S 3 :: (S 1 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 1 true (S 4) (S 5) 5 (S 4 :: X) (S 2 :: (S 3 :: (S 1 :: []))) (by rfl)
  have h7 : run base 3 (boundary 1 true (S 5 :: (S 4 :: X)) (S 2 :: (S 3 :: (S 1 :: [])))) = some (boundary 1 true (S 5 :: S 5 :: (S 4 :: X)) (S 3 :: (S 1 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 1 1 true (S 2) (S 5) 3 (S 5 :: (S 4 :: X)) (S 3 :: (S 1 :: [])) (by rfl)
  have h8 : run base 1 (boundary 1 true (S 5 :: S 5 :: (S 4 :: X)) (S 3 :: (S 1 :: []))) = some (boundary 3 false (S 5 :: S 5 :: (S 4 :: X)) (S 2 :: (S 1 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 1 3 false (S 3) (S 2) 1 (S 5 :: S 5 :: (S 4 :: X)) (S 1 :: []) (by rfl)
  have h9 : run base 3 (boundary 3 false (S 5 :: S 5 :: (S 4 :: X)) (S 2 :: (S 1 :: []))) = some (boundary 3 false (S 5 :: (S 4 :: X)) (S 4 :: (S 2 :: (S 1 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 3 false (S 5) (S 4) 3 (S 5 :: (S 4 :: X)) (S 2 :: (S 1 :: [])) (by rfl)
  have h10 : run base 3 (boundary 3 false (S 5 :: (S 4 :: X)) (S 4 :: (S 2 :: (S 1 :: [])))) = some (boundary 3 false (S 4 :: X) (S 4 :: S 4 :: (S 2 :: (S 1 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 3 false (S 5) (S 4) 3 (S 4 :: X) (S 4 :: (S 2 :: (S 1 :: []))) (by rfl)
  have h11 : run base 7 (boundary 3 false (S 4 :: X) (S 4 :: S 4 :: (S 2 :: (S 1 :: [])))) = some (boundary 4 true (S 1 :: X) (S 4 :: S 4 :: (S 2 :: (S 1 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 4 true (S 4) (S 1) 7 X (S 4 :: S 4 :: (S 2 :: (S 1 :: []))) (by rfl)
  have h12 : run base 1 (boundary 4 true (S 1 :: X) (S 4 :: S 4 :: (S 2 :: (S 1 :: [])))) = some (boundary 1 false (S 1 :: X) (S 4 :: S 4 :: (S 2 :: (S 1 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 4) (S 4) 1 (S 1 :: X) (S 4 :: (S 2 :: (S 1 :: []))) (by rfl)
  have h13 : run base 1 (boundary 1 false (S 1 :: X) (S 4 :: S 4 :: (S 2 :: (S 1 :: [])))) = some (boundary 2 true (S 5 :: X) (S 4 :: S 4 :: (S 2 :: (S 1 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 1) (S 5) 1 X (S 4 :: S 4 :: (S 2 :: (S 1 :: []))) (by rfl)
  have h14 : run base 3 (boundary 2 true (S 5 :: X) (S 4 :: S 4 :: (S 2 :: (S 1 :: [])))) = some (boundary 3 false (S 5 :: X) (S 6 :: (S 4 :: (S 2 :: (S 1 :: []))))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 3 false (S 4) (S 6) 3 (S 5 :: X) (S 4 :: (S 2 :: (S 1 :: []))) (by rfl)
  exact (join (join (join (join (join (join (join (join (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14)

theorem tail6421 (X : List Sym) : run base (5+1+1+3+7+1+1+5+1+1+7+1+1+7+3+5+1+3+3+7+1+1+3) (boundary 2 true (S 4 :: X) (S 6 :: (S 4 :: (S 2 :: (S 1 :: []))))) = some (boundary 3 false (S 5 :: X) (S 6 :: (S 4 :: (S 0 :: (S 5 :: []))))) := by
  have h0 : run base 5 (boundary 2 true (S 4 :: X) (S 6 :: (S 4 :: (S 2 :: (S 1 :: []))))) = some (boundary 4 true (S 0 :: (S 4 :: X)) (S 4 :: (S 2 :: (S 1 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 4 true (S 6) (S 0) 5 (S 4 :: X) (S 4 :: (S 2 :: (S 1 :: []))) (by rfl)
  have h1 : run base 1 (boundary 4 true (S 0 :: (S 4 :: X)) (S 4 :: (S 2 :: (S 1 :: [])))) = some (boundary 1 false (S 0 :: (S 4 :: X)) (S 4 :: (S 2 :: (S 1 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 4) (S 4) 1 (S 0 :: (S 4 :: X)) (S 2 :: (S 1 :: [])) (by rfl)
  have h2 : run base 1 (boundary 1 false (S 0 :: (S 4 :: X)) (S 4 :: (S 2 :: (S 1 :: [])))) = some (boundary 2 true (S 4 :: S 4 :: X) (S 4 :: (S 2 :: (S 1 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 0) (S 4) 1 (S 4 :: X) (S 4 :: (S 2 :: (S 1 :: []))) (by rfl)
  have h3 : run base 3 (boundary 2 true (S 4 :: S 4 :: X) (S 4 :: (S 2 :: (S 1 :: [])))) = some (boundary 3 false (S 4 :: S 4 :: X) (S 6 :: (S 2 :: (S 1 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 3 false (S 4) (S 6) 3 (S 4 :: S 4 :: X) (S 2 :: (S 1 :: [])) (by rfl)
  have h4 : run base 7 (boundary 3 false (S 4 :: S 4 :: X) (S 6 :: (S 2 :: (S 1 :: [])))) = some (boundary 4 true (S 1 :: (S 4 :: X)) (S 6 :: (S 2 :: (S 1 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 4 true (S 4) (S 1) 7 (S 4 :: X) (S 6 :: (S 2 :: (S 1 :: []))) (by rfl)
  have h5 : run base 1 (boundary 4 true (S 1 :: (S 4 :: X)) (S 6 :: (S 2 :: (S 1 :: [])))) = some (boundary 1 false (S 1 :: (S 4 :: X)) (S 6 :: (S 2 :: (S 1 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 6) (S 6) 1 (S 1 :: (S 4 :: X)) (S 2 :: (S 1 :: [])) (by rfl)
  have h6 : run base 1 (boundary 1 false (S 1 :: (S 4 :: X)) (S 6 :: (S 2 :: (S 1 :: [])))) = some (boundary 2 true (S 5 :: (S 4 :: X)) (S 6 :: (S 2 :: (S 1 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 1) (S 5) 1 (S 4 :: X) (S 6 :: (S 2 :: (S 1 :: []))) (by rfl)
  have h7 : run base 5 (boundary 2 true (S 5 :: (S 4 :: X)) (S 6 :: (S 2 :: (S 1 :: [])))) = some (boundary 4 true (S 0 :: (S 5 :: (S 4 :: X))) (S 2 :: (S 1 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 4 true (S 6) (S 0) 5 (S 5 :: (S 4 :: X)) (S 2 :: (S 1 :: [])) (by rfl)
  have h8 : run base 1 (boundary 4 true (S 0 :: (S 5 :: (S 4 :: X))) (S 2 :: (S 1 :: []))) = some (boundary 1 false (S 0 :: (S 5 :: (S 4 :: X))) (S 2 :: (S 1 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 2) (S 2) 1 (S 0 :: (S 5 :: (S 4 :: X))) (S 1 :: []) (by rfl)
  have h9 : run base 1 (boundary 1 false (S 0 :: (S 5 :: (S 4 :: X))) (S 2 :: (S 1 :: []))) = some (boundary 2 true (S 4 :: (S 5 :: (S 4 :: X))) (S 2 :: (S 1 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 0) (S 4) 1 (S 5 :: (S 4 :: X)) (S 2 :: (S 1 :: [])) (by rfl)
  have h10 : run base 7 (boundary 2 true (S 4 :: (S 5 :: (S 4 :: X))) (S 2 :: (S 1 :: []))) = some (boundary 3 true (S 6 :: (S 4 :: (S 5 :: (S 4 :: X)))) (S 1 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 3 true (S 2) (S 6) 7 (S 4 :: (S 5 :: (S 4 :: X))) (S 1 :: []) (by rfl)
  have h11 : run base 1 (boundary 3 true (S 6 :: (S 4 :: (S 5 :: (S 4 :: X)))) (S 1 :: [])) = some (boundary 4 false (S 6 :: (S 4 :: (S 5 :: (S 4 :: X)))) (S 1 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 3 4 false (S 1) (S 1) 1 (S 6 :: (S 4 :: (S 5 :: (S 4 :: X)))) [] (by rfl)
  have h12 : run base 1 (boundary 4 false (S 6 :: (S 4 :: (S 5 :: (S 4 :: X)))) (S 1 :: [])) = some (boundary 4 true (S 2 :: (S 4 :: (S 5 :: (S 4 :: X)))) (S 1 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 4 4 true (S 6) (S 2) 1 (S 4 :: (S 5 :: (S 4 :: X))) (S 1 :: []) (by rfl)
  have h13 : run base 7 (boundary 4 true (S 2 :: (S 4 :: (S 5 :: (S 4 :: X)))) (S 1 :: [])) = some (boundary 4 false (S 2 :: (S 4 :: (S 5 :: (S 4 :: X)))) (S 5 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 4 false (S 1) (S 5) 7 (S 2 :: (S 4 :: (S 5 :: (S 4 :: X)))) [] (by rfl)
  have h14 : run base 3 (boundary 4 false (S 2 :: (S 4 :: (S 5 :: (S 4 :: X)))) (S 5 :: [])) = some (boundary 1 false (S 4 :: (S 5 :: (S 4 :: X))) (S 1 :: (S 5 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 4 1 false (S 2) (S 1) 3 (S 4 :: (S 5 :: (S 4 :: X))) (S 5 :: []) (by rfl)
  have h15 : run base 5 (boundary 1 false (S 4 :: (S 5 :: (S 4 :: X))) (S 1 :: (S 5 :: []))) = some (boundary 1 true (S 5 :: S 5 :: (S 4 :: X)) (S 1 :: (S 5 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 1 true (S 4) (S 5) 5 (S 5 :: (S 4 :: X)) (S 1 :: (S 5 :: [])) (by rfl)
  have h16 : run base 1 (boundary 1 true (S 5 :: S 5 :: (S 4 :: X)) (S 1 :: (S 5 :: []))) = some (boundary 3 false (S 5 :: S 5 :: (S 4 :: X)) (S 0 :: (S 5 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 1 3 false (S 1) (S 0) 1 (S 5 :: S 5 :: (S 4 :: X)) (S 5 :: []) (by rfl)
  have h17 : run base 3 (boundary 3 false (S 5 :: S 5 :: (S 4 :: X)) (S 0 :: (S 5 :: []))) = some (boundary 3 false (S 5 :: (S 4 :: X)) (S 4 :: (S 0 :: (S 5 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 3 false (S 5) (S 4) 3 (S 5 :: (S 4 :: X)) (S 0 :: (S 5 :: [])) (by rfl)
  have h18 : run base 3 (boundary 3 false (S 5 :: (S 4 :: X)) (S 4 :: (S 0 :: (S 5 :: [])))) = some (boundary 3 false (S 4 :: X) (S 4 :: S 4 :: (S 0 :: (S 5 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 3 false (S 5) (S 4) 3 (S 4 :: X) (S 4 :: (S 0 :: (S 5 :: []))) (by rfl)
  have h19 : run base 7 (boundary 3 false (S 4 :: X) (S 4 :: S 4 :: (S 0 :: (S 5 :: [])))) = some (boundary 4 true (S 1 :: X) (S 4 :: S 4 :: (S 0 :: (S 5 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 4 true (S 4) (S 1) 7 X (S 4 :: S 4 :: (S 0 :: (S 5 :: []))) (by rfl)
  have h20 : run base 1 (boundary 4 true (S 1 :: X) (S 4 :: S 4 :: (S 0 :: (S 5 :: [])))) = some (boundary 1 false (S 1 :: X) (S 4 :: S 4 :: (S 0 :: (S 5 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 4) (S 4) 1 (S 1 :: X) (S 4 :: (S 0 :: (S 5 :: []))) (by rfl)
  have h21 : run base 1 (boundary 1 false (S 1 :: X) (S 4 :: S 4 :: (S 0 :: (S 5 :: [])))) = some (boundary 2 true (S 5 :: X) (S 4 :: S 4 :: (S 0 :: (S 5 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 1) (S 5) 1 X (S 4 :: S 4 :: (S 0 :: (S 5 :: []))) (by rfl)
  have h22 : run base 3 (boundary 2 true (S 5 :: X) (S 4 :: S 4 :: (S 0 :: (S 5 :: [])))) = some (boundary 3 false (S 5 :: X) (S 6 :: (S 4 :: (S 0 :: (S 5 :: []))))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 3 false (S 4) (S 6) 3 (S 5 :: X) (S 4 :: (S 0 :: (S 5 :: []))) (by rfl)
  exact (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15) h16) h17) h18) h19) h20) h21) h22)

theorem tail6405 (X : List Sym) : run base (5+1+1+3+7+1+1+5+1+1+3+7+1+1+7+1+1+7+1+1+3+3+3+3+3+7+1+1+3) (boundary 2 true (S 4 :: X) (S 6 :: (S 4 :: (S 0 :: (S 5 :: []))))) = some (boundary 3 false (S 5 :: X) (S 6 :: (S 2 :: (S 5 :: (S 4 :: (S 2 :: [])))))) := by
  have h0 : run base 5 (boundary 2 true (S 4 :: X) (S 6 :: (S 4 :: (S 0 :: (S 5 :: []))))) = some (boundary 4 true (S 0 :: (S 4 :: X)) (S 4 :: (S 0 :: (S 5 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 4 true (S 6) (S 0) 5 (S 4 :: X) (S 4 :: (S 0 :: (S 5 :: []))) (by rfl)
  have h1 : run base 1 (boundary 4 true (S 0 :: (S 4 :: X)) (S 4 :: (S 0 :: (S 5 :: [])))) = some (boundary 1 false (S 0 :: (S 4 :: X)) (S 4 :: (S 0 :: (S 5 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 4) (S 4) 1 (S 0 :: (S 4 :: X)) (S 0 :: (S 5 :: [])) (by rfl)
  have h2 : run base 1 (boundary 1 false (S 0 :: (S 4 :: X)) (S 4 :: (S 0 :: (S 5 :: [])))) = some (boundary 2 true (S 4 :: S 4 :: X) (S 4 :: (S 0 :: (S 5 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 0) (S 4) 1 (S 4 :: X) (S 4 :: (S 0 :: (S 5 :: []))) (by rfl)
  have h3 : run base 3 (boundary 2 true (S 4 :: S 4 :: X) (S 4 :: (S 0 :: (S 5 :: [])))) = some (boundary 3 false (S 4 :: S 4 :: X) (S 6 :: (S 0 :: (S 5 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 3 false (S 4) (S 6) 3 (S 4 :: S 4 :: X) (S 0 :: (S 5 :: [])) (by rfl)
  have h4 : run base 7 (boundary 3 false (S 4 :: S 4 :: X) (S 6 :: (S 0 :: (S 5 :: [])))) = some (boundary 4 true (S 1 :: (S 4 :: X)) (S 6 :: (S 0 :: (S 5 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 4 true (S 4) (S 1) 7 (S 4 :: X) (S 6 :: (S 0 :: (S 5 :: []))) (by rfl)
  have h5 : run base 1 (boundary 4 true (S 1 :: (S 4 :: X)) (S 6 :: (S 0 :: (S 5 :: [])))) = some (boundary 1 false (S 1 :: (S 4 :: X)) (S 6 :: (S 0 :: (S 5 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 6) (S 6) 1 (S 1 :: (S 4 :: X)) (S 0 :: (S 5 :: [])) (by rfl)
  have h6 : run base 1 (boundary 1 false (S 1 :: (S 4 :: X)) (S 6 :: (S 0 :: (S 5 :: [])))) = some (boundary 2 true (S 5 :: (S 4 :: X)) (S 6 :: (S 0 :: (S 5 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 1) (S 5) 1 (S 4 :: X) (S 6 :: (S 0 :: (S 5 :: []))) (by rfl)
  have h7 : run base 5 (boundary 2 true (S 5 :: (S 4 :: X)) (S 6 :: (S 0 :: (S 5 :: [])))) = some (boundary 4 true (S 0 :: (S 5 :: (S 4 :: X))) (S 0 :: (S 5 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 4 true (S 6) (S 0) 5 (S 5 :: (S 4 :: X)) (S 0 :: (S 5 :: [])) (by rfl)
  have h8 : run base 1 (boundary 4 true (S 0 :: (S 5 :: (S 4 :: X))) (S 0 :: (S 5 :: []))) = some (boundary 1 false (S 0 :: (S 5 :: (S 4 :: X))) (S 0 :: (S 5 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 0) (S 0) 1 (S 0 :: (S 5 :: (S 4 :: X))) (S 5 :: []) (by rfl)
  have h9 : run base 1 (boundary 1 false (S 0 :: (S 5 :: (S 4 :: X))) (S 0 :: (S 5 :: []))) = some (boundary 2 true (S 4 :: (S 5 :: (S 4 :: X))) (S 0 :: (S 5 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 0) (S 4) 1 (S 5 :: (S 4 :: X)) (S 0 :: (S 5 :: [])) (by rfl)
  have h10 : run base 3 (boundary 2 true (S 4 :: (S 5 :: (S 4 :: X))) (S 0 :: (S 5 :: []))) = some (boundary 3 false (S 4 :: (S 5 :: (S 4 :: X))) (S 2 :: (S 5 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 3 false (S 0) (S 2) 3 (S 4 :: (S 5 :: (S 4 :: X))) (S 5 :: []) (by rfl)
  have h11 : run base 7 (boundary 3 false (S 4 :: (S 5 :: (S 4 :: X))) (S 2 :: (S 5 :: []))) = some (boundary 4 true (S 1 :: (S 5 :: (S 4 :: X))) (S 2 :: (S 5 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 4 true (S 4) (S 1) 7 (S 5 :: (S 4 :: X)) (S 2 :: (S 5 :: [])) (by rfl)
  have h12 : run base 1 (boundary 4 true (S 1 :: (S 5 :: (S 4 :: X))) (S 2 :: (S 5 :: []))) = some (boundary 1 false (S 1 :: (S 5 :: (S 4 :: X))) (S 2 :: (S 5 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 2) (S 2) 1 (S 1 :: (S 5 :: (S 4 :: X))) (S 5 :: []) (by rfl)
  have h13 : run base 1 (boundary 1 false (S 1 :: (S 5 :: (S 4 :: X))) (S 2 :: (S 5 :: []))) = some (boundary 2 true (S 5 :: S 5 :: (S 4 :: X)) (S 2 :: (S 5 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 1) (S 5) 1 (S 5 :: (S 4 :: X)) (S 2 :: (S 5 :: [])) (by rfl)
  have h14 : run base 7 (boundary 2 true (S 5 :: S 5 :: (S 4 :: X)) (S 2 :: (S 5 :: []))) = some (boundary 3 true (S 6 :: (S 5 :: S 5 :: (S 4 :: X))) (S 5 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 3 true (S 2) (S 6) 7 (S 5 :: S 5 :: (S 4 :: X)) (S 5 :: []) (by rfl)
  have h15 : run base 1 (boundary 3 true (S 6 :: (S 5 :: S 5 :: (S 4 :: X))) (S 5 :: [])) = some (boundary 4 false (S 6 :: (S 5 :: S 5 :: (S 4 :: X))) (S 5 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 3 4 false (S 5) (S 5) 1 (S 6 :: (S 5 :: S 5 :: (S 4 :: X))) [] (by rfl)
  have h16 : run base 1 (boundary 4 false (S 6 :: (S 5 :: S 5 :: (S 4 :: X))) (S 5 :: [])) = some (boundary 4 true (S 2 :: (S 5 :: S 5 :: (S 4 :: X))) (S 5 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 4 4 true (S 6) (S 2) 1 (S 5 :: S 5 :: (S 4 :: X)) (S 5 :: []) (by rfl)
  have h17 : run base 7 (boundary 4 true (S 2 :: (S 5 :: S 5 :: (S 4 :: X))) (S 5 :: [])) = some (boundary 4 true (S 1 :: (S 2 :: (S 5 :: S 5 :: (S 4 :: X)))) []) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 4 true (S 5) (S 1) 7 (S 2 :: (S 5 :: S 5 :: (S 4 :: X))) [] (by rfl)
  have h18 : run base 1 (boundary 4 true (S 1 :: (S 2 :: (S 5 :: S 5 :: (S 4 :: X)))) []) = some (boundary 1 false (S 1 :: (S 2 :: (S 5 :: S 5 :: (S 4 :: X)))) []) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 0) (S 0) 1 (S 1 :: (S 2 :: (S 5 :: S 5 :: (S 4 :: X)))) [] (by rfl)
  have h19 : run base 1 (boundary 1 false (S 1 :: (S 2 :: (S 5 :: S 5 :: (S 4 :: X)))) []) = some (boundary 2 true (S 5 :: (S 2 :: (S 5 :: S 5 :: (S 4 :: X)))) []) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 1) (S 5) 1 (S 2 :: (S 5 :: S 5 :: (S 4 :: X))) [] (by rfl)
  have h20 : run base 3 (boundary 2 true (S 5 :: (S 2 :: (S 5 :: S 5 :: (S 4 :: X)))) []) = some (boundary 3 false (S 5 :: (S 2 :: (S 5 :: S 5 :: (S 4 :: X)))) (S 2 :: [])) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 3 false (S 0) (S 2) 3 (S 5 :: (S 2 :: (S 5 :: S 5 :: (S 4 :: X)))) [] (by rfl)
  have h21 : run base 3 (boundary 3 false (S 5 :: (S 2 :: (S 5 :: S 5 :: (S 4 :: X)))) (S 2 :: [])) = some (boundary 3 false (S 2 :: (S 5 :: S 5 :: (S 4 :: X))) (S 4 :: (S 2 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 3 false (S 5) (S 4) 3 (S 2 :: (S 5 :: S 5 :: (S 4 :: X))) (S 2 :: []) (by rfl)
  have h22 : run base 3 (boundary 3 false (S 2 :: (S 5 :: S 5 :: (S 4 :: X))) (S 4 :: (S 2 :: []))) = some (boundary 1 false (S 5 :: S 5 :: (S 4 :: X)) (S 5 :: (S 4 :: (S 2 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 1 false (S 2) (S 5) 3 (S 5 :: S 5 :: (S 4 :: X)) (S 4 :: (S 2 :: [])) (by rfl)
  have h23 : run base 3 (boundary 1 false (S 5 :: S 5 :: (S 4 :: X)) (S 5 :: (S 4 :: (S 2 :: [])))) = some (boundary 3 false (S 5 :: (S 4 :: X)) (S 2 :: (S 5 :: (S 4 :: (S 2 :: []))))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 3 false (S 5) (S 2) 3 (S 5 :: (S 4 :: X)) (S 5 :: (S 4 :: (S 2 :: []))) (by rfl)
  have h24 : run base 3 (boundary 3 false (S 5 :: (S 4 :: X)) (S 2 :: (S 5 :: (S 4 :: (S 2 :: []))))) = some (boundary 3 false (S 4 :: X) (S 4 :: (S 2 :: (S 5 :: (S 4 :: (S 2 :: [])))))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 3 false (S 5) (S 4) 3 (S 4 :: X) (S 2 :: (S 5 :: (S 4 :: (S 2 :: [])))) (by rfl)
  have h25 : run base 7 (boundary 3 false (S 4 :: X) (S 4 :: (S 2 :: (S 5 :: (S 4 :: (S 2 :: [])))))) = some (boundary 4 true (S 1 :: X) (S 4 :: (S 2 :: (S 5 :: (S 4 :: (S 2 :: [])))))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 4 true (S 4) (S 1) 7 X (S 4 :: (S 2 :: (S 5 :: (S 4 :: (S 2 :: []))))) (by rfl)
  have h26 : run base 1 (boundary 4 true (S 1 :: X) (S 4 :: (S 2 :: (S 5 :: (S 4 :: (S 2 :: [])))))) = some (boundary 1 false (S 1 :: X) (S 4 :: (S 2 :: (S 5 :: (S 4 :: (S 2 :: [])))))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 4) (S 4) 1 (S 1 :: X) (S 2 :: (S 5 :: (S 4 :: (S 2 :: [])))) (by rfl)
  have h27 : run base 1 (boundary 1 false (S 1 :: X) (S 4 :: (S 2 :: (S 5 :: (S 4 :: (S 2 :: [])))))) = some (boundary 2 true (S 5 :: X) (S 4 :: (S 2 :: (S 5 :: (S 4 :: (S 2 :: [])))))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 1) (S 5) 1 X (S 4 :: (S 2 :: (S 5 :: (S 4 :: (S 2 :: []))))) (by rfl)
  have h28 : run base 3 (boundary 2 true (S 5 :: X) (S 4 :: (S 2 :: (S 5 :: (S 4 :: (S 2 :: [])))))) = some (boundary 3 false (S 5 :: X) (S 6 :: (S 2 :: (S 5 :: (S 4 :: (S 2 :: [])))))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 3 false (S 4) (S 6) 3 (S 5 :: X) (S 2 :: (S 5 :: (S 4 :: (S 2 :: [])))) (by rfl)
  exact (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15) h16) h17) h18) h19) h20) h21) h22) h23) h24) h25) h26) h27) h28)

theorem tail62542 (X : List Sym) : run base (5+1+1+7+1+1+7+1+1+3+3+3+5+1+3+7+1+1+3) (boundary 2 true (S 4 :: X) (S 6 :: (S 2 :: (S 5 :: (S 4 :: (S 2 :: [])))))) = some (boundary 3 false (S 5 :: X) (S 6 :: (S 4 :: S 4 :: (S 6 :: (S 2 :: []))))) := by
  have h0 : run base 5 (boundary 2 true (S 4 :: X) (S 6 :: (S 2 :: (S 5 :: (S 4 :: (S 2 :: [])))))) = some (boundary 4 true (S 0 :: (S 4 :: X)) (S 2 :: (S 5 :: (S 4 :: (S 2 :: []))))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 4 true (S 6) (S 0) 5 (S 4 :: X) (S 2 :: (S 5 :: (S 4 :: (S 2 :: [])))) (by rfl)
  have h1 : run base 1 (boundary 4 true (S 0 :: (S 4 :: X)) (S 2 :: (S 5 :: (S 4 :: (S 2 :: []))))) = some (boundary 1 false (S 0 :: (S 4 :: X)) (S 2 :: (S 5 :: (S 4 :: (S 2 :: []))))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 2) (S 2) 1 (S 0 :: (S 4 :: X)) (S 5 :: (S 4 :: (S 2 :: []))) (by rfl)
  have h2 : run base 1 (boundary 1 false (S 0 :: (S 4 :: X)) (S 2 :: (S 5 :: (S 4 :: (S 2 :: []))))) = some (boundary 2 true (S 4 :: S 4 :: X) (S 2 :: (S 5 :: (S 4 :: (S 2 :: []))))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 0) (S 4) 1 (S 4 :: X) (S 2 :: (S 5 :: (S 4 :: (S 2 :: [])))) (by rfl)
  have h3 : run base 7 (boundary 2 true (S 4 :: S 4 :: X) (S 2 :: (S 5 :: (S 4 :: (S 2 :: []))))) = some (boundary 3 true (S 6 :: (S 4 :: S 4 :: X)) (S 5 :: (S 4 :: (S 2 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 3 true (S 2) (S 6) 7 (S 4 :: S 4 :: X) (S 5 :: (S 4 :: (S 2 :: []))) (by rfl)
  have h4 : run base 1 (boundary 3 true (S 6 :: (S 4 :: S 4 :: X)) (S 5 :: (S 4 :: (S 2 :: [])))) = some (boundary 4 false (S 6 :: (S 4 :: S 4 :: X)) (S 5 :: (S 4 :: (S 2 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 3 4 false (S 5) (S 5) 1 (S 6 :: (S 4 :: S 4 :: X)) (S 4 :: (S 2 :: [])) (by rfl)
  have h5 : run base 1 (boundary 4 false (S 6 :: (S 4 :: S 4 :: X)) (S 5 :: (S 4 :: (S 2 :: [])))) = some (boundary 4 true (S 2 :: (S 4 :: S 4 :: X)) (S 5 :: (S 4 :: (S 2 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 4 4 true (S 6) (S 2) 1 (S 4 :: S 4 :: X) (S 5 :: (S 4 :: (S 2 :: []))) (by rfl)
  have h6 : run base 7 (boundary 4 true (S 2 :: (S 4 :: S 4 :: X)) (S 5 :: (S 4 :: (S 2 :: [])))) = some (boundary 4 true (S 1 :: (S 2 :: (S 4 :: S 4 :: X))) (S 4 :: (S 2 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 4 true (S 5) (S 1) 7 (S 2 :: (S 4 :: S 4 :: X)) (S 4 :: (S 2 :: [])) (by rfl)
  have h7 : run base 1 (boundary 4 true (S 1 :: (S 2 :: (S 4 :: S 4 :: X))) (S 4 :: (S 2 :: []))) = some (boundary 1 false (S 1 :: (S 2 :: (S 4 :: S 4 :: X))) (S 4 :: (S 2 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 4) (S 4) 1 (S 1 :: (S 2 :: (S 4 :: S 4 :: X))) (S 2 :: []) (by rfl)
  have h8 : run base 1 (boundary 1 false (S 1 :: (S 2 :: (S 4 :: S 4 :: X))) (S 4 :: (S 2 :: []))) = some (boundary 2 true (S 5 :: (S 2 :: (S 4 :: S 4 :: X))) (S 4 :: (S 2 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 1) (S 5) 1 (S 2 :: (S 4 :: S 4 :: X)) (S 4 :: (S 2 :: [])) (by rfl)
  have h9 : run base 3 (boundary 2 true (S 5 :: (S 2 :: (S 4 :: S 4 :: X))) (S 4 :: (S 2 :: []))) = some (boundary 3 false (S 5 :: (S 2 :: (S 4 :: S 4 :: X))) (S 6 :: (S 2 :: []))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 3 false (S 4) (S 6) 3 (S 5 :: (S 2 :: (S 4 :: S 4 :: X))) (S 2 :: []) (by rfl)
  have h10 : run base 3 (boundary 3 false (S 5 :: (S 2 :: (S 4 :: S 4 :: X))) (S 6 :: (S 2 :: []))) = some (boundary 3 false (S 2 :: (S 4 :: S 4 :: X)) (S 4 :: (S 6 :: (S 2 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 3 false (S 5) (S 4) 3 (S 2 :: (S 4 :: S 4 :: X)) (S 6 :: (S 2 :: [])) (by rfl)
  have h11 : run base 3 (boundary 3 false (S 2 :: (S 4 :: S 4 :: X)) (S 4 :: (S 6 :: (S 2 :: [])))) = some (boundary 1 false (S 4 :: S 4 :: X) (S 5 :: (S 4 :: (S 6 :: (S 2 :: []))))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 1 false (S 2) (S 5) 3 (S 4 :: S 4 :: X) (S 4 :: (S 6 :: (S 2 :: []))) (by rfl)
  have h12 : run base 5 (boundary 1 false (S 4 :: S 4 :: X) (S 5 :: (S 4 :: (S 6 :: (S 2 :: []))))) = some (boundary 1 true (S 5 :: (S 4 :: X)) (S 5 :: (S 4 :: (S 6 :: (S 2 :: []))))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 1 true (S 4) (S 5) 5 (S 4 :: X) (S 5 :: (S 4 :: (S 6 :: (S 2 :: [])))) (by rfl)
  have h13 : run base 1 (boundary 1 true (S 5 :: (S 4 :: X)) (S 5 :: (S 4 :: (S 6 :: (S 2 :: []))))) = some (boundary 3 false (S 5 :: (S 4 :: X)) (S 4 :: S 4 :: (S 6 :: (S 2 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 1 3 false (S 5) (S 4) 1 (S 5 :: (S 4 :: X)) (S 4 :: (S 6 :: (S 2 :: []))) (by rfl)
  have h14 : run base 3 (boundary 3 false (S 5 :: (S 4 :: X)) (S 4 :: S 4 :: (S 6 :: (S 2 :: [])))) = some (boundary 3 false (S 4 :: X) (S 4 :: S 4 :: S 4 :: (S 6 :: (S 2 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 3 false (S 5) (S 4) 3 (S 4 :: X) (S 4 :: S 4 :: (S 6 :: (S 2 :: []))) (by rfl)
  have h15 : run base 7 (boundary 3 false (S 4 :: X) (S 4 :: S 4 :: S 4 :: (S 6 :: (S 2 :: [])))) = some (boundary 4 true (S 1 :: X) (S 4 :: S 4 :: S 4 :: (S 6 :: (S 2 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 4 true (S 4) (S 1) 7 X (S 4 :: S 4 :: S 4 :: (S 6 :: (S 2 :: []))) (by rfl)
  have h16 : run base 1 (boundary 4 true (S 1 :: X) (S 4 :: S 4 :: S 4 :: (S 6 :: (S 2 :: [])))) = some (boundary 1 false (S 1 :: X) (S 4 :: S 4 :: S 4 :: (S 6 :: (S 2 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 4) (S 4) 1 (S 1 :: X) (S 4 :: S 4 :: (S 6 :: (S 2 :: []))) (by rfl)
  have h17 : run base 1 (boundary 1 false (S 1 :: X) (S 4 :: S 4 :: S 4 :: (S 6 :: (S 2 :: [])))) = some (boundary 2 true (S 5 :: X) (S 4 :: S 4 :: S 4 :: (S 6 :: (S 2 :: [])))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 1) (S 5) 1 X (S 4 :: S 4 :: S 4 :: (S 6 :: (S 2 :: []))) (by rfl)
  have h18 : run base 3 (boundary 2 true (S 5 :: X) (S 4 :: S 4 :: S 4 :: (S 6 :: (S 2 :: [])))) = some (boundary 3 false (S 5 :: X) (S 6 :: (S 4 :: S 4 :: (S 6 :: (S 2 :: []))))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 3 false (S 4) (S 6) 3 (S 5 :: X) (S 4 :: S 4 :: (S 6 :: (S 2 :: []))) (by rfl)
  exact (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11) h12) h13) h14) h15) h16) h17) h18)

theorem dEnd (Y : List Sym) : run base (7+1+1+3+3) (boundary 3 false (S 4 :: []) (S 4 :: Y)) = some (boundary 3 false [] (S 4 :: (S 6 :: Y))) := by
  have h0 : run base 7 (boundary 3 false (S 4 :: []) (S 4 :: Y)) = some (boundary 4 true (S 1 :: []) (S 4 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 4 true (S 4) (S 1) 7 [] (S 4 :: Y) (by rfl)
  have h1 : run base 1 (boundary 4 true (S 1 :: []) (S 4 :: Y)) = some (boundary 1 false (S 1 :: []) (S 4 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 4) (S 4) 1 (S 1 :: []) Y (by rfl)
  have h2 : run base 1 (boundary 1 false (S 1 :: []) (S 4 :: Y)) = some (boundary 2 true (S 5 :: []) (S 4 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 1) (S 5) 1 [] (S 4 :: Y) (by rfl)
  have h3 : run base 3 (boundary 2 true (S 5 :: []) (S 4 :: Y)) = some (boundary 3 false (S 5 :: []) (S 6 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 3 false (S 4) (S 6) 3 (S 5 :: []) Y (by rfl)
  have h4 : run base 3 (boundary 3 false (S 5 :: []) (S 6 :: Y)) = some (boundary 3 false [] (S 4 :: (S 6 :: Y))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 3 false (S 5) (S 4) 3 [] (S 6 :: Y) (by rfl)
  exact (join (join (join (join h0 h1) h2) h3) h4)

theorem eTwo (X : List Sym) (Y : List Sym) : run base (5+1+1+3) (boundary 1 true (S 5 :: X) (S 4 :: S 4 :: Y)) = some (boundary 3 false (S 5 :: S 5 :: X) (S 6 :: Y)) := by
  have h0 : run base 5 (boundary 1 true (S 5 :: X) (S 4 :: S 4 :: Y)) = some (boundary 4 true (S 1 :: (S 5 :: X)) (S 4 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 1 4 true (S 4) (S 1) 5 (S 5 :: X) (S 4 :: Y) (by rfl)
  have h1 : run base 1 (boundary 4 true (S 1 :: (S 5 :: X)) (S 4 :: Y)) = some (boundary 1 false (S 1 :: (S 5 :: X)) (S 4 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 4) (S 4) 1 (S 1 :: (S 5 :: X)) Y (by rfl)
  have h2 : run base 1 (boundary 1 false (S 1 :: (S 5 :: X)) (S 4 :: Y)) = some (boundary 2 true (S 5 :: S 5 :: X) (S 4 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 1) (S 5) 1 (S 5 :: X) (S 4 :: Y) (by rfl)
  have h3 : run base 3 (boundary 2 true (S 5 :: S 5 :: X) (S 4 :: Y)) = some (boundary 3 false (S 5 :: S 5 :: X) (S 6 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 3 false (S 4) (S 6) 3 (S 5 :: S 5 :: X) Y (by rfl)
  exact (join (join (join h0 h1) h2) h3)

theorem eOne (X : List Sym) (Y : List Sym) : run base (5+1+1+5+1+1) (boundary 1 true (S 5 :: X) (S 4 :: (S 6 :: (S 4 :: Y)))) = some (boundary 2 true (S 4 :: (S 5 :: S 5 :: X)) (S 4 :: Y)) := by
  have h0 : run base 5 (boundary 1 true (S 5 :: X) (S 4 :: (S 6 :: (S 4 :: Y)))) = some (boundary 4 true (S 1 :: (S 5 :: X)) (S 6 :: (S 4 :: Y))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 1 4 true (S 4) (S 1) 5 (S 5 :: X) (S 6 :: (S 4 :: Y)) (by rfl)
  have h1 : run base 1 (boundary 4 true (S 1 :: (S 5 :: X)) (S 6 :: (S 4 :: Y))) = some (boundary 1 false (S 1 :: (S 5 :: X)) (S 6 :: (S 4 :: Y))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 6) (S 6) 1 (S 1 :: (S 5 :: X)) (S 4 :: Y) (by rfl)
  have h2 : run base 1 (boundary 1 false (S 1 :: (S 5 :: X)) (S 6 :: (S 4 :: Y))) = some (boundary 2 true (S 5 :: S 5 :: X) (S 6 :: (S 4 :: Y))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 1) (S 5) 1 (S 5 :: X) (S 6 :: (S 4 :: Y)) (by rfl)
  have h3 : run base 5 (boundary 2 true (S 5 :: S 5 :: X) (S 6 :: (S 4 :: Y))) = some (boundary 4 true (S 0 :: (S 5 :: S 5 :: X)) (S 4 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 4 true (S 6) (S 0) 5 (S 5 :: S 5 :: X) (S 4 :: Y) (by rfl)
  have h4 : run base 1 (boundary 4 true (S 0 :: (S 5 :: S 5 :: X)) (S 4 :: Y)) = some (boundary 1 false (S 0 :: (S 5 :: S 5 :: X)) (S 4 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 4) (S 4) 1 (S 0 :: (S 5 :: S 5 :: X)) Y (by rfl)
  have h5 : run base 1 (boundary 1 false (S 0 :: (S 5 :: S 5 :: X)) (S 4 :: Y)) = some (boundary 2 true (S 4 :: (S 5 :: S 5 :: X)) (S 4 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 0) (S 4) 1 (S 5 :: S 5 :: X) (S 4 :: Y) (by rfl)
  exact (join (join (join (join (join h0 h1) h2) h3) h4) h5)

theorem f13start (X : List Sym) (Y : List Sym) : run base (5+1+1) (boundary 2 true X (S 6 :: (S 4 :: Y))) = some (boundary 2 true (S 4 :: X) (S 4 :: Y)) := by
  have h0 : run base 5 (boundary 2 true X (S 6 :: (S 4 :: Y))) = some (boundary 4 true (S 0 :: X) (S 4 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 4 true (S 6) (S 0) 5 X (S 4 :: Y) (by rfl)
  have h1 : run base 1 (boundary 4 true (S 0 :: X) (S 4 :: Y)) = some (boundary 1 false (S 0 :: X) (S 4 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 4 1 false (S 4) (S 4) 1 (S 0 :: X) Y (by rfl)
  have h2 : run base 1 (boundary 1 false (S 0 :: X) (S 4 :: Y)) = some (boundary 2 true (S 4 :: X) (S 4 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 0) (S 4) 1 X (S 4 :: Y) (by rfl)
  exact (join (join h0 h1) h2)

theorem cr4turn (X : List Sym) (Y : List Sym) : run base (3) (boundary 2 true X (S 4 :: Y)) = some (boundary 3 false X (S 6 :: Y)) := by
  have h0 : run base 3 (boundary 2 true X (S 4 :: Y)) = some (boundary 3 false X (S 6 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 3 false (S 4) (S 6) 3 X Y (by rfl)
  exact h0

theorem reset4 (X : List Sym) (Y : List Sym) : run M4 (3+1+3) (boundary 1 true (S 5 :: X) (S 6 :: (S 4 :: S 4 :: Y))) = some (boundary 3 false (S 5 :: X) (S 2 :: (S 4 :: S 4 :: Y))) := by
  have h0 : run M4 3 (boundary 1 true (S 5 :: X) (S 6 :: (S 4 :: S 4 :: Y))) = some (boundary 5 true (S 5 :: S 5 :: X) (S 4 :: S 4 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR M4 1 5 true (S 6) (S 5) 3 (S 5 :: X) (S 4 :: S 4 :: Y) (by rfl)
  have h1 : run M4 1 (boundary 5 true (S 5 :: S 5 :: X) (S 4 :: S 4 :: Y)) = some (boundary 1 false (S 5 :: S 5 :: X) (S 4 :: S 4 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR M4 5 1 false (S 4) (S 4) 1 (S 5 :: S 5 :: X) (S 4 :: Y) (by rfl)
  have h2 : run M4 3 (boundary 1 false (S 5 :: S 5 :: X) (S 4 :: S 4 :: Y)) = some (boundary 3 false (S 5 :: X) (S 2 :: (S 4 :: S 4 :: Y))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL M4 1 3 false (S 5) (S 2) 3 (S 5 :: X) (S 4 :: S 4 :: Y) (by rfl)
  exact (join (join h0 h1) h2)

theorem reset13 (X : List Sym) (Y : List Sym) : run M13 (3+5+5+3+3) (boundary 1 true (S 5 :: X) (S 6 :: (S 4 :: S 4 :: (S 6 :: Y)))) = some (boundary 3 false (S 5 :: S 5 :: S 5 :: X) (S 2 :: (S 6 :: Y))) := by
  have h0 : run M13 3 (boundary 1 true (S 5 :: X) (S 6 :: (S 4 :: S 4 :: (S 6 :: Y)))) = some (boundary 5 true (S 5 :: S 5 :: X) (S 4 :: S 4 :: (S 6 :: Y))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR M13 1 5 true (S 6) (S 5) 3 (S 5 :: X) (S 4 :: S 4 :: (S 6 :: Y)) (by rfl)
  have h1 : run M13 5 (boundary 5 true (S 5 :: S 5 :: X) (S 4 :: S 4 :: (S 6 :: Y))) = some (boundary 5 true (S 5 :: S 5 :: S 5 :: X) (S 4 :: (S 6 :: Y))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR M13 5 5 true (S 4) (S 5) 5 (S 5 :: S 5 :: X) (S 4 :: (S 6 :: Y)) (by rfl)
  have h2 : run M13 5 (boundary 5 true (S 5 :: S 5 :: S 5 :: X) (S 4 :: (S 6 :: Y))) = some (boundary 5 true (S 5 :: S 5 :: S 5 :: S 5 :: X) (S 6 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR M13 5 5 true (S 4) (S 5) 5 (S 5 :: S 5 :: S 5 :: X) (S 6 :: Y) (by rfl)
  have h3 : run M13 3 (boundary 5 true (S 5 :: S 5 :: S 5 :: S 5 :: X) (S 6 :: Y)) = some (boundary 1 false (S 5 :: S 5 :: S 5 :: S 5 :: X) (S 6 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR M13 5 1 false (S 6) (S 6) 3 (S 5 :: S 5 :: S 5 :: S 5 :: X) Y (by rfl)
  have h4 : run M13 3 (boundary 1 false (S 5 :: S 5 :: S 5 :: S 5 :: X) (S 6 :: Y)) = some (boundary 3 false (S 5 :: S 5 :: S 5 :: X) (S 2 :: (S 6 :: Y))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL M13 1 3 false (S 5) (S 2) 3 (S 5 :: S 5 :: S 5 :: X) (S 6 :: Y) (by rfl)
  exact (join (join (join (join h0 h1) h2) h3) h4)

theorem convert1 (p : Nat) (Y : List Sym) : run base ((p*3)+3+(p*3)+3+(p*3)+3+1+((p+2)*3)) (boundary 3 false (U 5 p) (S 2 :: Y)) = some (boundary 2 true (U 6 (p+2) ++ (S 4 :: [])) Y) := by
  have h0 : run base (p*3) (boundary 3 false (U 5 p) (S 2 :: Y)) = some (boundary 3 false [] (U 4 p ++ (S 2 :: Y))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using sweepL base 3 (S 5) (S 4) 3 p [] (S 2 :: Y) (by rfl)
  have h1 : run base 3 (boundary 3 false [] (U 4 p ++ (S 2 :: Y))) = some (boundary 0 true (S 2 :: []) (U 4 p ++ (S 2 :: Y))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 0 true (S 0) (S 2) 3 [] (U 4 p ++ (S 2 :: Y)) (by rfl)
  have h2 : run base (p*3) (boundary 0 true (S 2 :: []) (U 4 p ++ (S 2 :: Y))) = some (boundary 0 true (U 3 p ++ (S 2 :: [])) (S 2 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using sweepR base 0 (S 4) (S 3) 3 p (S 2 :: []) (S 2 :: Y) (by rfl)
  have h3 : run base 3 (boundary 0 true (U 3 p ++ (S 2 :: [])) (S 2 :: Y)) = some (boundary 4 false (U 3 p ++ (S 2 :: [])) (S 1 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 0 4 false (S 2) (S 1) 3 (U 3 p ++ (S 2 :: [])) Y (by rfl)
  have h4 : run base (p*3) (boundary 4 false (U 3 p ++ (S 2 :: [])) (S 1 :: Y)) = some (boundary 4 false (S 2 :: []) (U 1 (p+1) ++ Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using sweepL base 4 (S 3) (S 1) 3 p (S 2 :: []) (S 1 :: Y) (by rfl)
  have h5 : run base 3 (boundary 4 false (S 2 :: []) (U 1 (p+1) ++ Y)) = some (boundary 1 false [] (U 1 (p+2) ++ Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 4 1 false (S 2) (S 1) 3 [] (U 1 (p+1) ++ Y) (by rfl)
  have h6 : run base 1 (boundary 1 false [] (U 1 (p+2) ++ Y)) = some (boundary 2 true (S 4 :: []) (U 1 (p+2) ++ Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 0) (S 4) 1 [] (U 1 (p+2) ++ Y) (by rfl)
  have h7 : run base ((p+2)*3) (boundary 2 true (S 4 :: []) (U 1 (p+2) ++ Y)) = some (boundary 2 true (U 6 (p+2) ++ (S 4 :: [])) Y) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using sweepR base 2 (S 1) (S 6) 3 (p+2) (S 4 :: []) Y (by rfl)
  exact (join (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6) h7)

theorem convert2 (p : Nat) (Y : List Sym) : run base (3+(p*3)+3+(p*3)+3+1+((p+1)*3)+5+((p+1)*3)+5+((p+2)*3)) (boundary 3 false [] (U 4 p ++ (S 6 :: Y))) = some (boundary 1 true (U 5 (p+3)) Y) := by
  have h0 : run base 3 (boundary 3 false [] (U 4 p ++ (S 6 :: Y))) = some (boundary 0 true (S 2 :: []) (U 4 p ++ (S 6 :: Y))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 3 0 true (S 0) (S 2) 3 [] (U 4 p ++ (S 6 :: Y)) (by rfl)
  have h1 : run base (p*3) (boundary 0 true (S 2 :: []) (U 4 p ++ (S 6 :: Y))) = some (boundary 0 true (U 3 p ++ (S 2 :: [])) (S 6 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using sweepR base 0 (S 4) (S 3) 3 p (S 2 :: []) (S 6 :: Y) (by rfl)
  have h2 : run base 3 (boundary 0 true (U 3 p ++ (S 2 :: [])) (S 6 :: Y)) = some (boundary 4 false (U 3 p ++ (S 2 :: [])) (S 5 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 0 4 false (S 6) (S 5) 3 (U 3 p ++ (S 2 :: [])) Y (by rfl)
  have h3 : run base (p*3) (boundary 4 false (U 3 p ++ (S 2 :: [])) (S 5 :: Y)) = some (boundary 4 false (S 2 :: []) (U 1 p ++ (S 5 :: Y))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using sweepL base 4 (S 3) (S 1) 3 p (S 2 :: []) (S 5 :: Y) (by rfl)
  have h4 : run base 3 (boundary 4 false (S 2 :: []) (U 1 p ++ (S 5 :: Y))) = some (boundary 1 false [] (U 1 (p+1) ++ (S 5 :: Y))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 4 1 false (S 2) (S 1) 3 [] (U 1 p ++ (S 5 :: Y)) (by rfl)
  have h5 : run base 1 (boundary 1 false [] (U 1 (p+1) ++ (S 5 :: Y))) = some (boundary 2 true (S 4 :: []) (U 1 (p+1) ++ (S 5 :: Y))) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 2 true (S 0) (S 4) 1 [] (U 1 (p+1) ++ (S 5 :: Y)) (by rfl)
  have h6 : run base ((p+1)*3) (boundary 2 true (S 4 :: []) (U 1 (p+1) ++ (S 5 :: Y))) = some (boundary 2 true (U 6 (p+1) ++ (S 4 :: [])) (S 5 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using sweepR base 2 (S 1) (S 6) 3 (p+1) (S 4 :: []) (S 5 :: Y) (by rfl)
  have h7 : run base 5 (boundary 2 true (U 6 (p+1) ++ (S 4 :: [])) (S 5 :: Y)) = some (boundary 1 false (U 6 (p+1) ++ (S 4 :: [])) (S 2 :: Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepR base 2 1 false (S 5) (S 2) 5 (U 6 (p+1) ++ (S 4 :: [])) Y (by rfl)
  have h8 : run base ((p+1)*3) (boundary 1 false (U 6 (p+1) ++ (S 4 :: [])) (S 2 :: Y)) = some (boundary 1 false (S 4 :: []) (U 2 (p+2) ++ Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using sweepL base 1 (S 6) (S 2) 3 (p+1) (S 4 :: []) (S 2 :: Y) (by rfl)
  have h9 : run base 5 (boundary 1 false (S 4 :: []) (U 2 (p+2) ++ Y)) = some (boundary 1 true (S 5 :: []) (U 2 (p+2) ++ Y)) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using stepL base 1 1 true (S 4) (S 5) 5 [] (U 2 (p+2) ++ Y) (by rfl)
  have h10 : run base ((p+2)*3) (boundary 1 true (S 5 :: []) (U 2 (p+2) ++ Y)) = some (boundary 1 true (U 5 (p+3)) Y) := by
    simpa only [U, List.replicate_succ, List.cons_append, List.append_assoc, List.append_nil, List.nil_append, Bool.false_eq_true, ite_false, ite_true, rep_cons, Szero, left_zero, right_zero] using sweepR base 1 (S 2) (S 5) 3 (p+2) (S 5 :: []) Y (by rfl)
  exact (join (join (join (join (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10)

#print axioms convert1
#print axioms convert2
#print axioms tail6405
end Raw140Double
