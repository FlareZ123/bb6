import Root119BShield
namespace BB6Root119
set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- Executable Boolean witness predicate over the literal 1289-step original run. -/
private def sharpCheck (n : Nat) : Bool :=
  match run n blank with
  | none => false
  | some d =>
    (d.q == Q.B) && !d.tape d.h &&
    d.tape (d.h-3) && !d.tape (d.h-2) &&
    d.tape (d.h+1) && d.tape (d.h+2) &&
    d.tape (d.h+3) && d.tape (d.h+4) && !d.tape (d.h+5)

/-- No all-time root theorem for this left sector can demand five right ones. -/
theorem original_blank_right_four_is_sharp :
    ∃ d : Conf, Reach d ∧ d.q = .B ∧ d.tape d.h = false ∧
      d.tape (d.h-3) = true ∧ d.tape (d.h-2) = false ∧
      d.tape (d.h+1) = true ∧ d.tape (d.h+2) = true ∧
      d.tape (d.h+3) = true ∧ d.tape (d.h+4) = true ∧
      d.tape (d.h+5) = false := by
  have heval : sharpCheck 1289 = true := by decide
  cases hr : run 1289 blank with
  | none =>
    simp [sharpCheck, hr] at heval
  | some d =>
    simp only [sharpCheck, hr, Bool.and_eq_true] at heval
    simp at heval
    refine ⟨d, reachable_of_run 1289 blank d Reach.initial hr, ?_⟩
    rcases heval with ⟨⟨⟨⟨⟨⟨⟨⟨hq,h0⟩,h3⟩,h2⟩,hr1⟩,hr2⟩,hr3⟩,hr4⟩,hr5⟩
    exact ⟨hq,h0,h3,h2,hr1,hr2,hr3,hr4,hr5⟩

#print axioms BB6Root119.original_blank_right_four_is_sharp
end BB6Root119
