import BB429Rank
import EscapeRay
import Lean.Elab.Tactic.Omega

/-!
A uniform source-matched ray-entry construction for the BB429 accelerator.
Every exact first counter u has infinitely many synthetically nonhalting
second-counter seeds. This is not an authentic blank reachability claim.
-/
namespace BB429GeneralEscape
open BB429 BB429Escape

/-- First counter after k consecutive long-first transitions from initial u. -/
def ray (u : Nat) : Nat → Nat
  | 0 => u
  | k+1 => 2*ray u k+3

/-- Cumulative second-counter subtraction along the same burst. -/
def demand (u : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => demand u k+ray u (k+1)

/-- Arbitrary-source, all-parameter exact first-burst lemma. -/
theorem generic_ray_run (u k W : Nat) (h : demand u k ≤ W) :
    run k (u,W) = some (ray u k,W-demand u k) := by
  induction k with
  | zero => simp [run,ray,demand]
  | succ k ih =>
    have hd : demand u k ≤ W := by simp only [demand] at h; omega
    have hs : 2*ray u k+3 ≤ W-demand u k := by
      simp only [demand,ray] at h
      omega
    simp only [run,ih hd,Option.bind_some]
    simp only [next,ge_iff_le,if_pos hs,ray,demand]
    simp only [Nat.sub_sub,Nat.add_assoc]

/-- Exact synthetic second counter whose first burst lands on the certified ray. -/
def seed (u k : Nat) : Nat := demand u k+ray u k+8

theorem seed_entry (u k : Nat) :
    run k (u,seed u k) = some (ray u k,ray u k+8) := by
  have hd : demand u k ≤ seed u k := by unfold seed; omega
  have hr := generic_ray_run u k (seed u k) hd
  have hs : seed u k-demand u k=ray u k+8 := by unfold seed; omega
  simpa only [hs] using hr

/-- For a fixed first counter, the nonhalting seed grows strictly with depth. -/
theorem seed_strict (u k : Nat) : seed u k < seed u (k+1) := by
  simp only [seed,demand,ray]
  omega

/-- From depth two, every ray first counter is 1 modulo 4. -/
theorem ray_mod_four (u k : Nat) (hk : 2 ≤ k) : ray u k % 4=1 := by
  cases k with
  | zero => omega
  | succ k =>
    cases k with
    | zero => omega
    | succ k =>
      change (2*(2*ray u k+3)+3)%4=1
      omega

/-- From depth three, every ray first counter is at least 21. -/
theorem ray_large (u k : Nat) (hk : 3 ≤ k) : 17 ≤ ray u k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hlarge : 3 ≤ k
    · have hh := ih hlarge
      simp only [ray]
      omega
    · have htwo : k=2 := by omega
      subst k
      simp only [ray]
      omega

/-- Every exact first counter admits infinitely many source-valid
synthetic starting configurations whose full forward orbit never halts. -/
theorem synthetic_never (u k n : Nat) (hk : 3 ≤ k) :
    run n (u,seed u k) ≠ none :=
  line_entry_never (u,seed u k) (ray u k) k n
    (ray_large u k hk) (ray_mod_four u k (by omega)) (seed_entry u k)

/-- Closed form for the first counter, without integer subtraction. -/
theorem ray_pow (u k : Nat) : ray u k+3=(u+3)*2^k := by
  induction k with
  | zero => simp [ray]
  | succ k ih =>
    calc
      ray u (k+1)+3 = 2*(ray u k+3) := by simp only [ray]; omega
      _ = (u+3)*2^(k+1) := by rw [ih,Nat.pow_succ]; simp [Nat.mul_assoc, Nat.mul_comm]

/-- Exact balance law for first-burst subtraction. -/
theorem demand_balance (u k : Nat) :
    demand u k+2*u+3*k=2*ray u k := by
  induction k with
  | zero => simp [ray,demand]
  | succ k ih =>
    simp only [demand,ray]
    omega

/-- Generalization of the previous u=0 and u=11 synthetic rays:
seed(u,k) + 2u + 3k +1 =3(u+3)2^k. -/
theorem seed_closed_form (u k : Nat) :
    seed u k+2*u+3*k+1=3*(u+3)*2^k := by
  have hp:=ray_pow u k
  have hb:=demand_balance u k
  calc
    seed u k+2*u+3*k+1 = 3*(ray u k+3) := by unfold seed; omega
    _ = 3*(u+3)*2^k := by rw [hp]; simp [Nat.mul_assoc]

#print axioms generic_ray_run
#print axioms seed_strict
#print axioms synthetic_never
#print axioms seed_closed_form
end BB429GeneralEscape
