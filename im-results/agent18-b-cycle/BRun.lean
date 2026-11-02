module

public import Agent18BReduction

@[expose] public section

namespace BB6.IterBridge
open BReduction

/-- Finite application of the partial acceleration, before optional halting. -/
def runN : Nat → Option S → Option S
  | 0,s => s
  | n+1,s => runN n (s.bind nextB)

/-- An exact local existential form of CollatzHalts. -/
def RunHalts (s : S) : Prop := ∃ n : Nat, (runN n (some s)).isNone

private theorem iter_from_some (n : Nat) (s : S) :
    runN (n+1) (some s) = runN n (nextB s) := by
  rfl

theorem inductive_to_iter (s : S) (h : Halts s) : RunHalts s := by
  induction h with
  | @stop s hs =>
      refine ⟨1, ?_⟩
      simp [hs, runN]
  | @next s t hs ht ih =>
      rcases ih with ⟨n,hn⟩
      refine ⟨n+1, ?_⟩
      rw [iter_from_some,hs]
      exact hn

theorem iter_to_inductive (n : Nat) (s : S)
    (h : (runN n (some s)).isNone) : Halts s := by
  induction n generalizing s with
  | zero =>
      simp [runN] at h
  | succ n ih =>
      rw [iter_from_some] at h
      cases hs : nextB s with
      | none => exact Halts.stop hs
      | some t =>
          rw [hs] at h
          exact Halts.next hs (ih t h)

theorem halts_iff_runN (s : S) : Halts s ↔ RunHalts s := by
  constructor
  · exact inductive_to_iter s
  · rintro ⟨n,hn⟩
    exact iter_to_inductive n s hn

#print axioms halts_iff_runN
end BB6.IterBridge
