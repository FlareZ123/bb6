import Mod512Source
import ResetEven
import Lean.Elab.Tactic.Omega

namespace BB6.Agent2F321ResetMod512
open BB6.Agent31F321Density
open BB6.Agent31F321Mod512
open BB6.Agent2F321Diagonal
open BB6.Agent2F321Bulk

/-- Every modulo-512 lift of (126 mod 256, 2) is absent from the
    accepted conservative source graph. -/
theorem forbidden_reset126_mod256 :
    ∀ r : Fin 512, r.val % 256 = 126 → hit r.val 2 = false := by
  decide +kernel

theorem reached_not_reset126_mod256 {n a : Nat}
    (hr : CounterReach 1 1 n a 2) :
    a % 256 ≠ 126 := by
  intro ha
  rcases source_reached_live_or_seed hr with hseed | hl
  · omega
  · let r : Fin 512 := ⟨a % 512, Nat.mod_lt _ (by decide)⟩
    have hr256 : r.val % 256 = 126 := by
      dsimp [r]
      omega
    have hf := forbidden_reset126_mod256 r hr256
    have hf' : hit a 2 = false := by
      simpa [hit, r, Nat.mod_mod] using hf
    rw [hf'] at hl
    contradiction

/-- Root-reachable middle-even reset-to-halt High runs cannot have
    length 123 modulo 256. -/
theorem middleEven_high_terminal_not_mod256_123
    {n k a d A D : Nat}
    (hr : CounterReach 1 1 n a d)
    (h1 : a < d) (h2 : d < 3*a+1) (hp : (d-a)%2 = 0)
    (hh : BB6.Agent2F321Bulk.HighRun k (4*a+6) 2 A D)
    (ht : A = D + 1) :
    k % 256 ≠ 123 := by
  intro hk
  have hreset : CounterReach 1 1 (n+1) (4*a+6) 2 :=
    CounterReach.step hr (CounterMove.middleEven d h1 h2 hp)
  have hforbid := reached_not_reset126_mod256 hreset
  apply hforbid
  have heq := BB6.Agent2F321Bulk.high_run_terminal_equation hh ht
  have hkge : 8 ≤ k := by omega
  have hdvd : 256 ∣ 2^k := by
    simpa using (Nat.pow_dvd_pow 2 hkge)
  obtain ⟨q,hq⟩ := hdvd
  rw [hq] at heq
  unfold BB6.Agent2F321Diagonal.X BB6.Agent2F321Diagonal.Y at heq
  omega

#print axioms forbidden_reset126_mod256
#print axioms reached_not_reset126_mod256
#print axioms middleEven_high_terminal_not_mod256_123
end BB6.Agent2F321ResetMod512
