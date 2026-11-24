import SourceDensity
import RouteBlock

namespace BB6.Agent26.HaltCylinders
open CryptidBoundary BB6.Padding BB6.BoundaryPadding
open BB6.Agent32Route (sect Walk walk_lift walk_source)

/-- The existing route DAG's entire certified family is transported through
    an arbitrary finite suffix, without enumerating the trillion paths. -/
theorem trillion_suffixes (w : List Bool) : ∃ R : List Nat,
    R.length=1057916215296 ∧ R.Nodup ∧
    ∀ a∈R, a<3^(108+zeros w) ∧
      ∀ n, 2≤n → n%3^(108+zeros w)=a → Halts (sec n w) := by
  obtain ⟨R,hlen,hnd,hR⟩ := BB6.Agent32Route.trillion_halting_cylinders
  obtain ⟨S,hs,hns,hS⟩ := suffix_family 108 R w hnd (unary_family_bridge 108 R hR)
  exact ⟨S,hs.trans hlen,hns,hS⟩

theorem unary_cylinder_exists : ∃ c, ∀ n, 2≤n → n%3^108=c%3^108 → Halts (sect n []) := by
  obtain ⟨R,hlen,hnd,hR⟩ := BB6.Agent32Route.trillion_halting_cylinders
  cases R with
  | nil => simp at hlen
  | cons c cs =>
    have hc := hR c (by simp)
    exact ⟨c,fun n hn hr => hc.2 n hn (by simpa [Nat.mod_eq_of_lt hc.1] using hr)⟩

theorem walk_liftable {n m L : Nat} {v w : List Bool} (h : Walk n v L m w) :
    Liftable n m L v w := fun q => walk_source (walk_lift h q)

theorem walk_target_ge {n m L : Nat} {v w : List Bool} (hn : 2≤n)
    (h : Walk n v L m w) : 2≤m := by
  induction h with
  | nil => exact hn
  | cons e k d m w he h ih =>
    apply ih
    unfold BB6.Agent32Route.AllCert.outputN
    omega

/-- A safe periodic invariant containing a certified walk's start must
    have period divisible by 3^(L+1), unless its period is zero. -/
theorem walk_periodic_obstruction {n m L s u : Nat} {v w : List Bool}
    (hn : 2≤n) (h : Walk n v L m w) (hs : s≤L) (hu : u%3≠0)
    (P : Nat → Prop) (hmem : P n)
    (hperiod : ∀ x, P x → P (x+3^s*u))
    (hsafe : ∀ x, P x → ¬Halts (sect x v)) : False := by
  obtain ⟨c,hc⟩ := unary_cylinder_exists
  exact source_periodic_obstruction 108 c L n m s u v w (walk_target_ge hn h) hs hu hc (walk_liftable h) P hmem hperiod hsafe

/-- Every positive period of any safe forward-periodic predicate through a
    section admitting a certified L-return walk has ternary valuation > L. -/
theorem walk_period_lower_bound {n m L M : Nat} {v w : List Bool}
    (hn : 2≤n) (h : Walk n v L m w) (hM : 0<M)
    (P : Nat → Prop) (hmem : P n)
    (hperiod : ∀ x, P x → P (x+M))
    (hsafe : ∀ x, P x → ¬Halts (sect x v)) : 3^(L+1) ∣ M := by
  obtain ⟨s,u,he,hu⟩ := factor_three M hM
  have hs : L+1≤s := by
    by_cases hlt : L+1≤s
    · exact hlt
    · exfalso
      exact walk_periodic_obstruction (s:=s) (u:=u) hn h (by omega) hu P hmem (by simpa [←he] using hperiod) hsafe
  refine ⟨3^(s-(L+1))*u,?_⟩
  rw [he,←Nat.mul_assoc,←Nat.pow_add,show L+1+(s-(L+1))=s by omega]

/-- Unbounded source-liftable prefixes exclude every positive period. -/
theorem no_periodic_safe_unbounded {n M : Nat} {v : List Bool}
    (hn : 2≤n) (hM : 0<M)
    (hwalk : ∀ L, ∃ m w, Walk n v L m w)
    (P : Nat → Prop) (hmem : P n)
    (hperiod : ∀ x, P x → P (x+M))
    (hsafe : ∀ x, P x → ¬Halts (sect x v)) : False := by
  obtain ⟨s,u,he,hu⟩ := factor_three M hM
  obtain ⟨m,w,h⟩ := hwalk s
  exact walk_periodic_obstruction hn h (Nat.le_refl _) hu P hmem (by simpa [←he] using hperiod) hsafe

#print axioms trillion_suffixes
#print axioms walk_period_lower_bound
#print axioms no_periodic_safe_unbounded
end BB6.Agent26.HaltCylinders
