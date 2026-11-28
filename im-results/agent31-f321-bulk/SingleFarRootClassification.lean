import TerminalWordOneFar
import HighFarRootTargets
import Mod384Source
import Lean.Elab.Tactic.Omega

/-!
Complete root classification of the F321 terminal suffix whose forward H/F
language is High^n followed by one final Far.

The earlier HighFarTerminalFamily constructed the n = 24k+22 family as an
infinite source-faithful danger family.  This file proves the converse at the
authentic source root: every root-reachable small-second state supporting a
terminal inverse word highThenFar n is forced into exactly that family.

The new ingredient is the accepted conservative modulo-384 source graph.  At
second counter 1 it permits only first-counter residues 6,8,14,22 modulo 24
apart from the blank seed itself.  The exact terminal equation and d == 1
(mod 6) force d == 13 (mod 24), so the inverse-word sum equation eliminates
all n == 4 (mod 6) phases except n == 22 (mod 24).

No anchor-decomposition theorem is used here: the hypothesis is an authentic
CounterReach witness from (1,1), so this result is independent of the pending
Agent2 AnchorEpoch development.
-/

set_option maxRecDepth 200000

namespace BB6.Agent31F321SingleFar
open BB6.Agent31F321Density
open BB6.Agent31F321Mod384
open BB6.Agent31F321HighFarFamily
open BB6.Agent31F321HighFarRootTargets
open BB6.Agent2F321Phase6Bridge

/-- Exact finite projection of the accepted mod-384 overapproximation at
    second counter 1. -/
theorem live_second_one_mod24 :
    ∀ r : Fin 384, hit r.val 1 = true →
      r.val % 24 = 6 ∨ r.val % 24 = 8 ∨
      r.val % 24 = 14 ∨ r.val % 24 = 22 := by
  decide +kernel

/-- Every source-reached state with second counter 1 is either the blank seed
    itself or lies in one of the four mod-24 classes admitted by the
    conservative source quotient. -/
theorem reached_second_one_mod24_or_seed
    {m R : Nat}
    (hr : CounterReach 1 1 m R 1) :
    R = 1 ∨
      R % 24 = 6 ∨ R % 24 = 8 ∨
      R % 24 = 14 ∨ R % 24 = 22 := by
  rcases source_reached_live_or_seed hr with hseed | hl
  · exact Or.inl hseed.1
  · right
    let r : Fin 384 := ⟨R % 384, Nat.mod_lt _ (by decide)⟩
    have hrLive : hit r.val 1 = true := by
      simpa [r, hit, Nat.mod_mod] using hl
    have ht := live_second_one_mod24 r hrLive
    dsimp [r] at ht
    rcases ht with h6 | h8 | h14 | h22 <;> omega

/-- Exact sum decrease of the High^n/F inverse word. -/
theorem highThenFar_sumDecrease (n : Nat) :
    (compile (highThenFar n)).sumDecrease = n+6 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [highThenFar, compile, advance, ih]

/-- The mod-384 source quotient plus the exact one-F terminal equation collapses
    the root-compatible High-count phase from n == 4 (mod 6) to the single
    class n == 22 (mod 24). -/
theorem highThenFar_root_mod24
    {m n d R c : Nat}
    (hroot : CounterReach 1 1 m R c)
    (hc : c=1 ∨ c=2)
    (hd6 : d % 6 = 1)
    (hp : FormalInversePath (d:Int) (highThenFar n) (R:Int) (c:Int)) :
    c = 1 ∧ n % 24 = 22 := by
  have hphase := highThenFar_root_phase hc hd6 hp
  have hc1 : c=1 := hphase.1
  have hn6 : n%6=4 := hphase.2
  subst c

  have hcand := formal_inverse_terminal_candidate hp
  rw [highThenFar_denom, highThenFar_num_one] at hcand
  have hdnat : 7*d = 2^(n+4)+3 := by
    exact_mod_cast hcand

  have hn4 : 4 ≤ n := by omega
  have hpow : 64 ∣ 2^(n+4) := by
    have hle : 6 ≤ n+4 := by omega
    simpa using (Nat.pow_dvd_pow 2 hle)
  obtain ⟨z,hz⟩ := hpow
  have hd64 : d%64=37 := by
    rw [hz] at hdnat
    omega
  have hd24 : d%24=13 := by omega

  have hsum := (formal_inverse_path_certificate hp).2
  unfold sumAt at hsum
  rw [highThenFar_sumDecrease] at hsum
  have hRsum : R+n+6=2*d := by omega

  have hR24 := reached_second_one_mod24_or_seed hroot

  constructor
  · rfl
  · rcases hR24 with hseed | h6 | h8 | h14 | h22 <;> omega

/-- Converse-complete identification: every authentic-root-compatible
    High^n/F terminal inverse suffix is exactly one member of the previously
    constructed danger family, including its terminal parameter and anchor. -/
theorem highThenFar_root_is_danger_family
    {m n d R c : Nat}
    (hroot : CounterReach 1 1 m R c)
    (hc : c=1 ∨ c=2)
    (hd6 : d % 6 = 1)
    (hp : FormalInversePath (d:Int) (highThenFar n) (R:Int) (c:Int)) :
    ∃ k,
      n = dangerN k ∧
      d = dangerT k ∧
      R = dangerR k ∧
      c = 1 := by
  have hphase := highThenFar_root_mod24 hroot hc hd6 hp
  have hc1 := hphase.1
  have hn24 := hphase.2
  subst c

  obtain ⟨k,hk⟩ : ∃ k, n=24*k+22 := by
    refine ⟨n/24, ?_⟩
    omega
  have hkN : n=dangerN k := by
    simpa [dangerN] using hk

  have hcand := formal_inverse_terminal_candidate hp
  rw [highThenFar_denom, highThenFar_num_one] at hcand
  have hdnat : 7*d = 2^(n+4)+3 := by
    exact_mod_cast hcand

  have hTeq0 := highFarT_equation (8*k+6)
  have hNk : highFarN (8*k+6) = dangerN k := by
    simp [highFarN, dangerN]
    omega
  rw [hNk] at hTeq0
  have hTeq : 7*dangerT k = 2^(dangerN k+4)+3 := by
    simpa [dangerT, dangerM] using hTeq0

  have hdT : d=dangerT k := by
    rw [hkN] at hdnat
    omega

  have hsum := (formal_inverse_path_certificate hp).2
  unfold sumAt at hsum
  rw [highThenFar_sumDecrease] at hsum
  have hRsum : R+n+6=2*d := by omega
  have hR : R=dangerR k := by
    unfold dangerR
    rw [← hdT, ← hkN]
    omega

  exact ⟨k,hkN,hdT,hR,rfl⟩

/-- Direct corollary for a genuine terminal gate: any source-root-compatible
    High^n/F suffix ending at that terminal is forced into the danger family. -/
theorem terminal_highThenFar_root_is_danger_family
    {N m n D R c : Nat}
    (hterm : CounterReach 1 1 (N+1) (D+1) D)
    (hroot : CounterReach 1 1 m R c)
    (hc : c=1 ∨ c=2)
    (hp : FormalInversePath (D:Int) (highThenFar n) (R:Int) (c:Int)) :
    ∃ k,
      n = dangerN k ∧
      D = dangerT k ∧
      R = dangerR k ∧
      c = 1 := by
  have hD6 := counterReach_terminal_mod6
    (n:=N+1) (d:=D) (by omega) hterm
  exact highThenFar_root_is_danger_family hroot hc hD6 hp

#print axioms live_second_one_mod24
#print axioms reached_second_one_mod24_or_seed
#print axioms highThenFar_sumDecrease
#print axioms highThenFar_root_mod24
#print axioms highThenFar_root_is_danger_family
#print axioms terminal_highThenFar_root_is_danger_family
end BB6.Agent31F321SingleFar
