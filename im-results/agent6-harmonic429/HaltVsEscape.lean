import GeneralEscape
import Lean.Elab.Tactic.Omega

/-!
Exact paired synthetic halting and nonhalting seeds for every BB429 first counter.
The two seeds execute the same number of first-branch transitions and
end in opposite halting behaviours. No claim about genuine blank reachability.
-/
namespace BB429HaltVsEscape
open BB429 BB429GeneralEscape

/-- A second-counter seed whose k first transitions end on the exact halt line. -/
def haltSeed (u k : Nat) : Nat := demand u k + (2*ray u k-1)

theorem ray_positive (u k : Nat) (hk : 1 ≤ k) : 3 ≤ ray u k := by
  cases k with
  | zero => omega
  | succ k => simp only [ray]; omega

theorem halt_seed_entry (u k : Nat) (hk : 1 ≤ k) :
    run k (u,haltSeed u k) = some (ray u k,2*ray u k-1) := by
  have hd : demand u k ≤ haltSeed u k := by unfold haltSeed; omega
  have hr := generic_ray_run u k (haltSeed u k) hd
  have hs : haltSeed u k-demand u k=2*ray u k-1 := by
    have hh:=ray_positive u k hk
    unfold haltSeed
    omega
  simpa only [hs] using hr

/-- The halting synthetic seed stops on its (k+1)-th accelerated instruction. -/
theorem halts_after_burst (u k : Nat) (hk : 1 ≤ k) :
    run (k+1) (u,haltSeed u k) = none := by
  have hr := halt_seed_entry u k hk
  have hpos := ray_positive u k hk
  have hg : (2*ray u k-1)+1=2*ray u k := by omega
  have hn : BB429.next (ray u k,2*ray u k-1) = none :=
    (BB429.next_none_iff_halt_line (ray u k) (2*ray u k-1)).mpr hg
  simp only [run, hr, Option.bind_some, hn]

/-- Closed-form arithmetic for the halting seed. -/
theorem halting_closed_form (u k : Nat) (hk : 1 ≤ k) :
    haltSeed u k+2*u+3*k+13=4*(u+3)*2^k := by
  have hbal:=demand_balance u k
  have hpow:=ray_pow u k
  have hpos:=ray_positive u k hk
  calc
    haltSeed u k+2*u+3*k+13 = 4*(ray u k+3) := by unfold haltSeed; omega
    _ = 4*(u+3)*2^k := by rw [hpow]; simp [Nat.mul_assoc]

/-- The halting start is exactly a-9 above the corresponding never-halting
start, where a is their common first counter after k steps. -/
theorem pair_gap (u k : Nat) (hk : 3 ≤ k) :
    seed u k + (ray u k-9) = haltSeed u k := by
  have hh := ray_large u k hk
  unfold seed haltSeed
  omega

/-- Explicit incompatible outcomes at arbitrarily large first-burst depths. -/
theorem incompatible_pair (u k : Nat) (hk : 3 ≤ k) :
    (∀ n, run n (u,seed u k) ≠ none) ∧
    run (k+1) (u,haltSeed u k) = none ∧
    seed u k < haltSeed u k := by
  constructor
  · intro n
    exact synthetic_never u k n hk
  constructor
  · exact halts_after_burst u k (by omega)
  · have hh := ray_large u k hk
    have he := pair_gap u k hk
    omega

#print axioms halts_after_burst
#print axioms halting_closed_form
#print axioms pair_gap
#print axioms incompatible_pair
end BB429HaltVsEscape
