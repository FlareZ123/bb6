import EqualHigh
import Mod384Source
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent2F321EqualHighMod384

open BB6.Agent2F321Diagonal
open BB6.Agent2F321Bulk
open BB6.Agent2F321EqualHigh
open BB6.Agent31F321Mod384

/-- The residue of the equal-reset predecessor forced by a terminal High run,
expressed only in terms of the run length modulo 768. -/
def equalHighTargetResidue (r : Nat) : Nat :=
  (256 + 384 - (((r+10)/2) % 384)) % 384

/-- The 24 residue classes modulo 768 that survive the source-certified
modulo-384 diagonal quotient. -/
def equalHighAllowedK768 : List Nat :=
  [36,60,84,90,156,180,252,258,324,354,378,420,
   444,468,474,492,498,540,564,636,642,708,738,762]

/-- A finite 768-case table.  The quotient hit is the kernel-checked
modulo-384 source invariant; this table performs no trajectory simulation. -/
theorem equalHighAllowedK768_table :
    ∀ r : Fin 768,
      (r.val % 24 = 12 ∨ r.val % 24 = 18) →
      hit (equalHighTargetResidue r.val) (equalHighTargetResidue r.val) = true →
      r.val ∈ equalHighAllowedK768 := by
  decide +kernel

private theorem pow2_even_mod384 (k : Nat)
    (hk : 8 ≤ k) (heven : k % 2 = 0) :
    2^k % 384 = 256 := by
  obtain ⟨u, hu⟩ : ∃ u : Nat, k = 8 + 2*u := by omega
  subst k
  induction u with
  | zero => decide
  | succ u ih =>
      have hexp : 8 + 2*(u+1) = (8+2*u)+2 := by omega
      rw [hexp, Nat.pow_add]
      have htwo : 2^2 = 4 := by decide
      rw [htwo, Nat.mul_mod, ih]

private theorem half_mod768 (k : Nat) (heven : k % 2 = 0) :
    ((k+10)/2) % 384 = (((k%768)+10)/2) % 384 := by
  omega

/-- Any root-reachable Equal predecessor that launches a terminal High run
must have its High length in these 24 classes modulo 768.  This refines the
coarser k mod 24 phase using the source-certified 384 quotient. -/
theorem equalHigh_root_k_mod768
    {n k a A D : Nat}
    (hn : 0 < n)
    (hr : CounterReach 1 1 n a a)
    (hh : HighRun k (2*a+4) 1 A D)
    (ht : A = D + 1) :
    k % 768 ∈ equalHighAllowedK768 := by
  have hphase := equal_high_terminal_length_mod24 hn hr hh ht
  have hk8 : 8 ≤ k := by
    rcases hphase with h | h <;> omega
  have hkeven : k % 2 = 0 := by
    rcases hphase with h | h <;> omega
  have hcoord := high_run_terminal_equation hh ht
  unfold X Y at hcoord
  have hformula : 2*a + k + 10 = 8 * 2^k := by omega
  have hsum : a + (k+10)/2 = 4 * 2^k := by omega
  have hpow := pow2_even_mod384 k hk8 hkeven
  have hpow4 : (4*2^k) % 384 = 256 := by
    rw [Nat.mul_mod, hpow]
    decide
  have hmodsum : (a + (k+10)/2) % 384 = 256 := by
    calc
      _ = (4*2^k) % 384 := by rw [hsum]
      _ = 256 := hpow4
  have hpred0 : a % 384 =
      (256 + 384 - (((k+10)/2) % 384)) % 384 := by omega
  have hhalf := half_mod768 k hkeven
  have hpred : a % 384 = equalHighTargetResidue (k%768) := by
    unfold equalHighTargetResidue
    rw [← hhalf]
    exact hpred0
  rcases source_reached_live_or_seed hr with hseed | hhit
  · have hx := counterReach_X_growth hr
    unfold X at hx
    omega
  · have hmods : a % 384 =
        (equalHighTargetResidue (k%768)) % 384 := by
      simpa [equalHighTargetResidue, Nat.mod_mod] using hpred
    have hdiag :
        hit (equalHighTargetResidue (k%768))
          (equalHighTargetResidue (k%768)) = true :=
      hit_of_mods hmods hmods hhit
    let r : Fin 768 := ⟨k%768, Nat.mod_lt _ (by decide)⟩
    have hrphase : r.val % 24 = 12 ∨ r.val % 24 = 18 := by
      simpa [r] using hphase
    have hrt :
        hit (equalHighTargetResidue r.val)
          (equalHighTargetResidue r.val) = true := by
      simpa [r] using hdiag
    exact equalHighAllowedK768_table r hrphase hrt

#print axioms equalHighAllowedK768_table
#print axioms equalHigh_root_k_mod768

end BB6.Agent2F321EqualHighMod384
