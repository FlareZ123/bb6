import CSection
import Lean.Elab.Tactic.Omega

namespace BB6.Agent8Depth
open BB6.CReachBridge BB6.CSection

/-- Middle-counter values admitting n repeated long-sector inverse returns. -/
def K : Nat → Nat → Nat
  | 0, u => u
  | n+1, u => 2 * K n u + 2

/-- Reset-gateway indices compatible with n repeated long-sector inverse returns. -/
def J : Nat → Nat → Nat
  | 0, j => j
  | n+1, j => 2 * J n j + 2

/-- An exact formal chain of n long-section predecessor relations,
    with every reverse middle counter positive. -/
inductive LongAnc : Nat → Nat → Nat → Prop
  | zero (a k : Nat) : LongAnc 0 a k
  | succ (n a k : Nat) (hk : 1 ≤ k)
      (h : LongAnc n (a + 2*k) k) : LongAnc (n+1) a (2*k+2)

theorem K_positive (n u : Nat) (hu : 1 ≤ u) : 1 ≤ K n u := by
  induction n with
  | zero => simpa only [K] using hu
  | succ n ih =>
      change 1 ≤ 2*K n u+2
      omega

theorem K_long_anc (n a u : Nat) (hu : 1 ≤ u) : LongAnc n a (K n u) := by
  induction n generalizing a with
  | zero => exact .zero a u
  | succ n ih =>
      change LongAnc (n+1) a (2*K n u+2)
      exact .succ n a (K n u) (K_positive n u hu) (ih (a+2*K n u))

theorem K_at_reset (n j : Nat) : K n (3*j+4) = 3*(J n j)+4 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change 2*K n (3*j+4)+2 = 3*(2*J n j+2)+4
      omega

theorem long_return (a k : Nat) (hk : 1 ≤ k) :
    runN (2*k+1) (some (a+2*k,k,0)) = some (a,2*k+2,0) := by
  obtain ⟨q,hq⟩ : ∃ q, k=q+1 := ⟨k-1, by omega⟩
  subst k
  have h := section_long q a
  simpa only [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using h

/-- Every LongAnc certificate gives a genuine finite computation of the
    unmodified Machine C counter map, with at least n accelerated calls. -/
theorem LongAnc_sound {n a k : Nat} (h : LongAnc n a k) :
    ∃ aa kk time : Nat, n ≤ time ∧
      runN time (some (aa,kk,0)) = some (a,k,0) := by
  induction h with
  | zero a k =>
      exact ⟨a,k,0,by omega,rfl⟩
  | succ n a k hk h ih =>
      obtain ⟨aa,kk,time,hbound,hrun⟩ := ih
      refine ⟨aa,kk,time+(2*k+1),by omega,?_⟩
      rw [runN_add,hrun]
      exact long_return a k hk

/-- For every n and j there is an n-link long-section inverse path
    ending in the Machine C reset gateway indexed by J n j. -/
theorem arbitrarily_deep_reset_ancestors (n j : Nat) :
    LongAnc n (2*(J n j)+1) (3*(J n j)+4) := by
  rw [← K_at_reset n j]
  exact K_long_anc n (2*(J n j)+1) (3*j+4) (by omega)

theorem J_ge (n j : Nat) : j ≤ J n j := by
  induction n with
  | zero => simp [J]
  | succ n ih =>
      change j ≤ 2*J n j+2
      omega

/-- Exact 2-adic family: j_n+2=2^n*(j_0+2). -/
theorem J_plus_two (n j : Nat) : J n j+2 = 2^n*(j+2) := by
  induction n with
  | zero => simp [J]
  | succ n ih =>
      change (2*J n j+2)+2 = 2^(n+1)*(j+2)
      calc
        (2*J n j+2)+2 = 2*(J n j+2) := by omega
        _ = 2*(2^n*(j+2)) := by rw [ih]
        _ = 2^(n+1)*(j+2) := by
          simp only [Nat.pow_succ]
          simp only [Nat.mul_comm, Nat.mul_left_comm]

/-- For every depth and threshold, a larger reset gateway has an n-link
    exact long-sector inverse chain; j+2 is divisible by 2^n. -/
theorem unbounded_reset_ancestor_depth (n lower : Nat) :
    ∃ j : Nat, lower < j ∧
      LongAnc n (2*j+1) (3*j+4) ∧
      ∃ q : Nat, j+2=2^n*q := by
  refine ⟨J n (lower+1), ?_, arbitrarily_deep_reset_ancestors n (lower+1), ?_⟩
  · have h := J_ge n (lower+1)
    omega
  · exact ⟨lower+3, J_plus_two n (lower+1)⟩

/-- Source-semantic accelerated runs from nonblank initial counter states. -/
theorem arbitrarily_deep_reset_traces (n j : Nat) :
    ∃ aa kk time : Nat, n ≤ time ∧
      runN time (some (aa,kk,0)) = some (2*(J n j)+1,3*(J n j)+4,0) :=
  LongAnc_sound (arbitrarily_deep_reset_ancestors n j)

#print axioms unbounded_reset_ancestor_depth
#print axioms arbitrarily_deep_reset_ancestors
#print axioms arbitrarily_deep_reset_traces
end BB6.Agent8Depth
