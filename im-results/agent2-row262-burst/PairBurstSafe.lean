import PairBurst
set_option maxHeartbeats 2000000
namespace BB6.Row262

def isHalt (c : Cfg) : Prop := c.st = 5 ∧ c.head = true

theorem halt_step_fixed (c : Cfg) (h : isHalt c) : step c = c := by
  rcases h with ⟨hs, hh⟩
  cases c with
  | mk st l hd r =>
      change st = 5 at hs
      change hd = true at hh
      subst st
      subst hd
      rfl

theorem halt_run_fixed (n : Nat) (c : Cfg) (h : isHalt c) : run n c = c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [run, halt_step_fixed c h]
      exact ih c h

-- Including the terminal checkpoint: the verified 9q source transition
-- shortcut has no frozen halting configuration in its entire raw prefix.
theorem pair_burst_no_halt (q t : Nat) (ls ys : List Bool)
    (ht : t ≤ 9*q) :
    ¬ isHalt (run t ⟨0,ls,false,[true,false] ++ rightBurst q ++ ys⟩) := by
  intro h
  let c : Cfg := ⟨0,ls,false,[true,false] ++ rightBurst q ++ ys⟩
  have hdecomp : t + (9*q - t) = 9*q := Nat.add_sub_of_le ht
  have hlast : run (9*q) c = run t c := by
    calc
      run (9*q) c = run (t+(9*q-t)) c := by rw [hdecomp]
      _ = run (9*q-t) (run t c) := run_add t (9*q-t) c
      _ = run t c := halt_run_fixed (9*q-t) (run t c) h
  have hfinal := pair_burst q ls ys
  change run (9*q) c = _ at hfinal
  rw [hfinal] at hlast
  have heq : (run t c).st = 0 := by rw [←hlast]
  have hst : (run t c).st = 5 := h.1
  omega

#print axioms BB6.Row262.halt_step_fixed
#print axioms BB6.Row262.halt_run_fixed
#print axioms BB6.Row262.pair_burst_no_halt
end BB6.Row262
