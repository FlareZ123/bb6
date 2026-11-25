import SweepPumping

set_option maxRecDepth 100000

namespace BB6Coverage.Agent31Pump

/-- Append an opaque, uninspected right-tape suffix to a zipper state. -/
def appendRight (z : Z0) (R : List Bool) : Z0 :=
  ⟨z.q, z.l, z.r ++ R⟩

/-- A single move preserves the appended suffix unless it moves right from
    the end of the finite visible prefix. -/
theorem move0_append_right (mv : Move) (z : Z0) (R : List Bool)
    (hsafe : mv.right = false ∨ z.r ≠ []) :
    move0 mv (appendRight z R) = appendRight (move0 mv z) R := by
  cases hr : z.r with
  | nil =>
      cases hright : mv.right
      · simp [move0, appendRight, hr, hright]
      · have hfalse : False := by
          rcases hsafe with h | h
          · simp [hright] at h
          · exact h hr
        exact False.elim hfalse
  | cons b bs =>
      cases hright : mv.right <;> simp [move0, appendRight, hr, hright]

/-- The safety condition for a finite run to be insensitive to an appended
    right suffix. Every rightward move must consume a cell from the visible
    finite prefix; leftward moves may occur even when that prefix is empty. -/
def SafeRight (p : PartialMachine) : Nat → Z0 → Prop
  | 0, _ => True
  | n+1, z =>
      ∃ mv, (p (z.q, z.l.headD false)).bind id = some mv ∧
        (mv.right = false ∨ z.r ≠ []) ∧
        SafeRight p n (move0 mv z)

/-- One transition commutes with appending an opaque right suffix, under the
    exact condition that a right move does not read beyond the visible prefix. -/
theorem step0_append_right (p : PartialMachine) (z : Z0) (R : List Bool)
    (mv : Move) (hm : (p (z.q, z.l.headD false)).bind id = some mv)
    (hsafe : mv.right = false ∨ z.r ≠ []) :
    step0 p (appendRight z R) = some (appendRight (move0 mv z) R) := by
  change ((p (z.q, z.l.headD false)).bind id).map
    (fun mv' => move0 mv' (appendRight z R)) =
    some (appendRight (move0 mv z) R)
  rw [hm]
  simp only [Option.map_some]
  exact congrArg some (move0_append_right mv z R hsafe)

/-- The ordinary finite-prefix step, used to identify the base run. -/
theorem step0_eq_of_move (p : PartialMachine) (z : Z0) (mv : Move)
    (hm : (p (z.q, z.l.headD false)).bind id = some mv) :
    step0 p z = some (move0 mv z) := by
  change ((p (z.q, z.l.headD false)).bind id).map
    (fun mv' => move0 mv' z) = some (move0 mv z)
  rw [hm]
  simp only [Option.map_some]

/-- Frame theorem: any safe finite run on a visible right-tape prefix extends
    unchanged to every arbitrary suffix. The suffix is never inspected or
    modified, and the final configuration carries it verbatim. -/
theorem run0_append_right_of_safe (p : PartialMachine) (n : Nat)
    (z : Z0) (R : List Bool) (hs : SafeRight p n z) :
    run0 p n (appendRight z R) =
      (run0 p n z).map (fun z' => appendRight z' R) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
      rcases hs with ⟨mv, hm, hsafe, htail⟩
      have hstep := step0_append_right p z R mv hm hsafe
      have hstep0 := step0_eq_of_move p z mv hm
      calc
        run0 p (n+1) (appendRight z R)
            = run0 p n (appendRight (move0 mv z) R) := by
                simp [run0, hstep]
        _ = (run0 p n (move0 mv z)).map (fun z' => appendRight z' R) :=
              ih (move0 mv z) htail
        _ = (run0 p (n+1) z).map (fun z' => appendRight z' R) := by
              simp [run0, hstep0]

/-- Convenient exact-output form for a concrete prefix macro. -/
theorem run0_append_right_of_safe_eq (p : PartialMachine) (n : Nat)
    (z z' : Z0) (R : List Bool)
    (hRun : run0 p n z = some z') (hs : SafeRight p n z) :
    run0 p n (appendRight z R) = some (appendRight z' R) := by
  rw [run0_append_right_of_safe p n z R hs, hRun]
  rfl

#print axioms move0_append_right
#print axioms run0_append_right_of_safe
#print axioms run0_append_right_of_safe_eq

end BB6Coverage.Agent31Pump
