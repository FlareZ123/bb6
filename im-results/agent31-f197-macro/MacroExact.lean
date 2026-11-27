import Macro

namespace F197

/-- Exact-cost iterator for the already-verified four-phase macro machine. -/
def macroRunExact : Nat → MacroConfig → Option (Nat × MacroConfig)
  | 0, m => some (0, m)
  | k+1, m =>
      match macroStep m with
      | none => none
      | some (n, m') =>
          match macroRunExact k m' with
          | none => none
          | some (s, m'') => some (n+s, m'')

theorem macroRunExact_sound (k : Nat) (m : MacroConfig) (tot : Nat)
    (m' : MacroConfig) (hv : valid m)
    (h : macroRunExact k m = some (tot, m')) :
    run tot (physical m) = some (physical m') := by
  induction k generalizing m tot m' with
  | zero =>
      simp [macroRunExact] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
  | succ k ih =>
      simp only [macroRunExact] at h
      cases hs : macroStep m with
      | none =>
          simp [hs] at h
      | some nm =>
          rcases nm with ⟨n, m1⟩
          simp only [hs] at h
          cases hr : macroRunExact k m1 with
          | none =>
              simp [hr] at h
          | some sm =>
              rcases sm with ⟨s, m2⟩
              simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              have hstep : run n (physical m) = some (physical m1) :=
                macro_sound hv hs
              have hv1 : valid m1 := (macro_valid hs).1
              have hrest : run s (physical m1) = some (physical m2) :=
                ih m1 s m2 hv1 hr
              rw [run_add, hstep]
              exact hrest

#print axioms macroRunExact_sound

end F197
