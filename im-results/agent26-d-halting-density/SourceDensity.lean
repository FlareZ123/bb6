import RouteFront
import PeriodicObstruction

namespace BB6.Agent26.HaltCylinders
open CryptidBoundary BB6.Padding BB6.BoundaryPadding
open BB6.Agent32Route

theorem padded_unary (n : Nat) : ObsEq (sec n []) (sect n []) := by
  refine ⟨tapeEq_refl _,rfl,?_,rfl⟩
  change TapeEq (List.replicate n true ++ []) (List.replicate n true ++ [false])
  simpa using tapeEq_pad (List.replicate n true) 1

theorem halt_obs {c d : Cfg} (h : ObsEq c d) : Halts c ↔ Halts d := by
  constructor
  · rintro ⟨t,ht⟩
    exact ⟨t,(source_congr t h).2.2.2.symm.trans ht⟩
  · rintro ⟨t,ht⟩
    exact ⟨t,(source_congr t h).2.2.2.trans ht⟩

theorem halt_obs_return {c d : Cfg} {t : Nat} (h : ObsEq (run t c) d)
    (hd : Halts d) : Halts c := by
  obtain ⟨s,hs⟩ := (halt_obs h).mpr hd
  exact ⟨t+s,by rw [run_add]; exact hs⟩

/-- The route DAG uses an explicit delimiter. Transfer any family in its
    unary convention to the exact physical section convention used here. -/
theorem unary_family_bridge (d : Nat) (R : List Nat)
    (hR : ∀ a∈R, a<3^d ∧ ∀ n, 2≤n → n%3^d=a → Halts (sect n [])) :
    ∀ a∈R, a<3^d ∧ ∀ n, 2≤n → n%3^d=a → Halts (sec n []) := by
  intro a ha
  refine ⟨(hR a ha).1,?_⟩
  intro n hn hr
  exact (halt_obs (padded_unary n)).mpr ((hR a ha).2 n hn hr)

/-- Sufficient source property for a finite prefix to establish the
    periodic obstruction. Each lift must have an exact raw execution. -/
def Liftable (n m L : Nat) (v w : List Bool) : Prop :=
  ∀ q, ∃ t, ObsEq (run t (sect (n+3^L*q) v)) (sect (m+8^L*q) w)

theorem liftable_halts (n m L : Nat) (v w : List Bool)
    (h : Liftable n m L v w) (q : Nat) :
    Halts (sec (m+8^L*q) (false::w)) → Halts (sec (n+3^L*q) (false::v)) := by
  obtain ⟨t,ht⟩ := h q
  exact halt_obs_return ht

/-- A positive period M whose ternary valuation is at most L is excluded
    as the period of any safe set containing the lifted source prefix. -/
theorem source_periodic_obstruction (d c L n m s u : Nat) (v w : List Bool)
    (hm : 2≤m) (hs : s≤L) (hu : u%3≠0)
    (hbase : ∀ z, 2≤z → z%3^d=c%3^d → Halts (sect z []))
    (h : Liftable n m L v w)
    (P : Nat → Prop) (hn : P n)
    (hperiod : ∀ x, P x → P (x+3^s*u))
    (hsafe : ∀ x, P x → ¬Halts (sect x v)) : False := by
  apply periodic_obstruction d c L n m s u (false::v) (false::w) hm hs hu _ (liftable_halts n m L v w h) P hn hperiod hsafe
  intro z hz hr
  exact (halt_obs (padded_unary z)).mpr (hbase z hz hr)

#print axioms unary_family_bridge
#print axioms source_periodic_obstruction
end BB6.Agent26.HaltCylinders
