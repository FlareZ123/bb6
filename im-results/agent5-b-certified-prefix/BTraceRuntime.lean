import BTraceMagnitude
import Agent18BReduction
import Lean.Elab.Tactic.Omega

namespace BB6.BTrace
open BB6.BReduction

/-- No positive-first-counter B transition decreases it by more than one. -/
theorem nextB_positive (s : S) (ha : 0 < s.1) :
    ∃ t : S, nextB s = some t ∧ s.1 ≤ t.1+1 := by
  rcases s with ⟨a,b,c⟩
  cases a with
  | zero => omega
  | succ a =>
    cases b with
    | zero => exact ⟨(a,c,2),rfl,by simp⟩
    | succ b =>
      cases b with
      | zero => exact ⟨(a,c,6),rfl,by simp⟩
      | succ b =>
          have hb : b+1+1 = b+2 := by omega
          rw [hb]
          exact ⟨(a+1,b,c+3),rfl,by simp⟩

def runB : Nat → S → Option S
  | 0,s => some s
  | n+1,s => (nextB s).bind (runB n)

theorem runB_positive_fuel (n : Nat) (s : S) (hn : n < s.1) :
    ∃ t : S, runB n s = some t := by
  induction n generalizing s with
  | zero => exact ⟨s,rfl⟩
  | succ n ih =>
      obtain ⟨t,ht,hdec⟩ := nextB_positive s (by omega)
      have hlt : n < t.1 := by omega
      obtain ⟨u,hu⟩ := ih t hlt
      exact ⟨u,by simpa [runB,ht] using hu⟩

/-- All first 2^132846 macro transitions after the fourth reset are defined. -/
theorem giant_postreset_prefix (n : Nat) (hn : n < 2^132846) :
    ∃ t : S, runB n (BB6.OneDim.scalarA 3,0,0) = some t := by
  exact runB_positive_fuel n _ (Nat.lt_of_lt_of_le hn fourth_reset_lower)

#print axioms nextB_positive
#print axioms runB_positive_fuel
#print axioms giant_postreset_prefix
end BB6.BTrace
