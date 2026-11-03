import DirectSource
import FastSectionProof
import Lean.Elab.Tactic.Omega

namespace BB6.Agent1Direct
open BB6.Agent46

/-- Exact number of original accelerated CLine calls in n consecutive
    source direct-section transitions. -/
def directTime (k : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => directTime k n + (2*(2^n*(k+2)-2)+1)

/-- A closed additive formula for all n and all natural initial right k. -/
theorem direct_time_closed (k n : Nat) :
    directTime k n + 2*(k+2) + 3*n = 2^(n+1)*(k+2) := by
  induction n with
  | zero => simp [directTime]
  | succ n ih =>
      have hn : 1≤2^n := Nat.one_le_pow n 2 (by decide)
      have hb : 2≤2^n*(k+2) := by
        have hh := Nat.mul_le_mul_right (k+2) hn
        omega
      have hpow : 2^((n+1)+1)*(k+2) = 4*(2^n*(k+2)) := by
        rw [Nat.pow_succ, Nat.pow_succ]
        have h4 : (4:Nat) = 2*2 := by decide
        rw [h4]
        ac_rfl
      have hpowprev : 2^(n+1)*(k+2) = 2*(2^n*(k+2)) := by
        rw [Nat.pow_succ]
        ac_rfl
      simp only [directTime]
      rw [hpow]
      rw [hpowprev] at ih
      omega

/-- The CLine time cost is determined by the right-counter gain. -/
theorem direct_time_counter {n a k x y : Nat} (h : Direct n a k x y) :
    directTime k n + 2*k + 3*n = 2*y := by
  have ht := direct_time_closed k n
  have hc := direct_counter h
  have he : 2^(n+1)*(k+2)=2*(2^n*(k+2)) := by
    rw [Nat.pow_succ]
    ac_rfl
  rw [he,←hc] at ht
  omega

/-- Exact potential: final first counter plus elapsed CLine calls
    equals initial first counter plus the number of direct returns. -/
theorem direct_time_potential {n a k x y : Nat} (h : Direct n a k x y) :
    x + directTime k n = a+n := by
  have ht := direct_time_counter h
  have hm := direct_mass h
  omega

#print axioms direct_time_potential

/-- Direct epoch costs are the sum of the true variable-length section
    excursions, with no formal shortcut or unproved shift in clock. -/
theorem direct_exact_cline {n a k x y : Nat}
    (h : Direct n a k x y) :
    BB6.Agent46.run (directTime k n) (some (a,k,0)) =
      some (x,y,0) := by
  induction h with
  | zero a k => rfl
  | @succ n a k b c h ha hk hg ih =>
      have hc := direct_counter h
      have htime : directTime k (n+1)=directTime k n+(2*c+1) := by
        simp only [directTime]
        omega
      rw [htime,BB6.Agent46.run_add,ih]
      rw [BB6.Agent46.run_eq]
      exact BB6.Agent46.section_dominant b c hk hg

/-- Completely explicit original CLine time and endpoint after a
    source-valid direct epoch certified by one arithmetic guard. -/
theorem source_direct_jump_timed (a k r : Nat) (hk : 0<k)
    (ha : Allowed a k r) :
    BB6.Agent46.run (directTime k (r+1)) (some (a,k,0)) =
      some ((directState a k (r+1)).1,
            (directState a k (r+1)).2,0) := by
  obtain ⟨x,y,hd⟩ := (direct_iff_last_guard a k r hk).mpr ha
  rw [direct_state_exact hd]
  exact direct_exact_cline hd

#print axioms direct_time_closed
#print axioms direct_exact_cline
#print axioms source_direct_jump_timed
end BB6.Agent1Direct
