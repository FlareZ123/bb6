import CQuarter
import CLine

namespace BB6Agent38

theorem source_next_agrees (s : S) : nextC s = BB6CLine.nextC s := by
  rfl

def sourceRun : Nat → Option S → Option S
  | 0, o => o
  | n+1, o => sourceRun n (o.bind BB6CLine.nextC)

theorem source_run_agrees (n : Nat) (o : Option S) :
    sourceRun n o = run n o := by
  induction n generalizing o with
  | zero => rfl
  | succ n ih =>
      simp only [sourceRun,run]
      rw [show o.bind BB6CLine.nextC = o.bind nextC from by
        cases o with
        | none => rfl
        | some s => simp [source_next_agrees]]
      exact ih _

/-- Source-level universal finite-target bound for the original published accelerator. -/
theorem source_hit_target_iff_quarter_bound (s t : S) :
    (∃ n, sourceRun n (some s) = some t) ↔
    (∃ n, 4*n ≤ rank t*(rank t+1) ∧ sourceRun n (some s) = some t) := by
  simpa only [source_run_agrees] using hit_target_iff_quarter_bound s t

/-- Specialized bound for Machine C's thin halting-gateway family. -/
theorem source_thin_cutoff (s : S) (j n : Nat)
    (h : sourceRun n (some s) = some (0,2*j,4*j+10)) :
    4*n ≤ (8*j+10)*(8*j+11)-2*(4*j+10) := by
  rw [source_run_agrees] at h
  have hp := energy_run n s (0,2*j,4*j+10) h
  have hbound : 4*n ≤ energy (0,2*j,4*j+10) := by omega
  have hrank : rank (0,2*j,4*j+10) = 8*j+10 := by
    simp only [rank]
    omega
  have hpot : potential (0,2*j,4*j+10) = 4*j+10 := by
    simp [potential]
  simpa only [energy,hrank,hpot] using hbound

#print axioms source_hit_target_iff_quarter_bound
#print axioms source_thin_cutoff
end BB6Agent38
