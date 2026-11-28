import SourceNextBridge
import Lean.Elab.Tactic.Omega
namespace BB6.Agent31F321Density

/-- Reflexive-transitive closure of the exact option-valued counter
    transition, from an arbitrary seed. -/
inductive NextReach (startA startD:Nat) : Nat → Nat → Nat → Prop where
 | nil : NextReach startA startD 0 startA startD
 | step {m a d A D:Nat}
    (hr:NextReach startA startD m a d)
    (hs:sourceNext a d=some (A,D)) :
    NextReach startA startD (m+1) A D

theorem next_reach_to_counter {sa sd m a d:Nat}
   (h:NextReach sa sd m a d) : CounterReach sa sd m a d := by
  induction h with
  | nil => exact CounterReach.nil
  | step hr hs ih => exact CounterReach.step ih (move_of_sourceNext_some hs)

theorem counter_to_next_reach {sa sd m a d:Nat}
   (h:CounterReach sa sd m a d) : NextReach sa sd m a d := by
  induction h with
  | nil => exact NextReach.nil
  | step hr hs ih => exact NextReach.step ih (sourceNext_some_of_move hs)

theorem next_reach_iff_counter {sa sd m a d:Nat} :
  NextReach sa sd m a d ↔ CounterReach sa sd m a d :=
   ⟨next_reach_to_counter,counter_to_next_reach⟩

/-- The exact executable counter program halts iff a terminal gate is
    reached from the genuine seed, with unbounded runtime. -/
theorem source_halts_iff_terminal_counter :
  (∃m a d, NextReach 1 1 m a d ∧ sourceNext a d=none) ↔
  (∃m d, CounterReach 1 1 m (d+1) d) := by
  constructor
  · rintro ⟨m,a,d,hr,hn⟩
    have ha : a=d+1 := (sourceNext_none_iff a d).mp hn
    subst a
    exact ⟨m,d,next_reach_to_counter hr⟩
  · rintro ⟨m,d,hr⟩
    exact ⟨m,d+1,d,counter_to_next_reach hr,
      (sourceNext_none_iff (d+1) d).mpr rfl⟩

/-- A finite modular certificate rules out all possible executable
    option-valued counter computations reaching their d-th halt. -/
theorem no_source_halt_at_terminal (n d:Nat)
    (hb:6*2^n≤d+3) (hs:residuePass n d=true) :
    ∀m, ¬(NextReach 1 1 m (d+1) d ∧ sourceNext (d+1) d=none) := by
  intro m h
  exact (no_halting_gate_after_decide n d hb hs m)
    (next_reach_to_counter h.1)

#print axioms source_halts_iff_terminal_counter
#print axioms no_source_halt_at_terminal
end BB6.Agent31F321Density
