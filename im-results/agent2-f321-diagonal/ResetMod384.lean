import Mod384Source
import ResetEven
import Phase6Bridge
import Lean.Elab.Tactic.Omega

namespace BB6.Agent2F321ResetMod384
open BB6.Agent31F321Density
open BB6.Agent31F321Mod384
open BB6.Agent2F321Diagonal
open BB6.Agent2F321Bulk
open BB6.Agent2F321Phase6
open BB6.Agent2F321ResetEven

/-- Every modulo-384 lift of the residue pair (30 mod 64, 2) is absent
    from the accepted conservative source graph. -/
theorem forbidden_reset30_mod64 :
    ∀ r : Fin 384, r.val % 64 = 30 → hit r.val 2 = false := by
  decide +kernel

/-- Consequently no authentic source state reached from (1,1) can have
    second counter 2 and first counter 30 modulo 64. -/
theorem reached_not_reset30_mod64 {n a : Nat}
    (hr : CounterReach 1 1 n a 2) :
    a % 64 ≠ 30 := by
  intro ha
  rcases source_reached_live_or_seed hr with hseed | hl
  · omega
  · let r : Fin 384 := ⟨a % 384, Nat.mod_lt _ (by decide)⟩
    have hr64 : r.val % 64 = 30 := by
      dsimp [r]
      omega
    have hf := forbidden_reset30_mod64 r hr64
    have hf' : hit a 2 = false := by
      simpa [hit, r, Nat.mod_mod] using hf
    rw [hf'] at hl
    contradiction

/-- A root-reachable middle-even reset followed only by High steps cannot
    terminate after a run of length 27 modulo 64.  This is an all-depth
    variable-run exclusion obtained by applying the existing finite quotient
    at the reset state rather than at the terminal gate. -/
theorem middleEven_high_terminal_not_mod64_27
    {n k a d A D : Nat}
    (hr : CounterReach 1 1 n a d)
    (h1 : a < d) (h2 : d < 3*a+1) (hp : (d-a)%2 = 0)
    (hh : HighRun k (4*a+6) 2 A D)
    (ht : A = D + 1) :
    k % 64 ≠ 27 := by
  intro hk
  have hreset : CounterReach 1 1 (n+1) (4*a+6) 2 :=
    CounterReach.step hr (CounterMove.middleEven d h1 h2 hp)
  have hforbid := reached_not_reset30_mod64 hreset
  apply hforbid
  have heq := high_run_terminal_equation hh ht
  have hkge : 6 ≤ k := by omega
  have hdvd : 64 ∣ 2^k := by
    simpa using (Nat.pow_dvd_pow 2 hkge)
  obtain ⟨q,hq⟩ := hdvd
  rw [hq] at heq
  unfold X Y at heq
  omega

#print axioms forbidden_reset30_mod64
#print axioms reached_not_reset30_mod64
#print axioms middleEven_high_terminal_not_mod64_27
end BB6.Agent2F321ResetMod384
