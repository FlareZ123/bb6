import Agent39DPeriodic

namespace BB6.Agent39

/-!
Branch-independent lower bounds directly visible in the source-checked
conditional D F-return tables. The E-zero-double offset 3 explains the sole
small-index exception n=4; every section from n>=5 strictly increases.
-/
def DOffsetBounds (rule : Nat → Nat → Option (Nat × Nat)) : Prop :=
  (∀ s c t, rule 2 s = some (c,t) → 9 ≤ c) ∧
  (∀ s c t, rule 3 s = some (c,t) → 7 ≤ c) ∧
  (∀ s c t, rule 4 s = some (c,t) → 3 ≤ c)

theorem affine_step_grows_from_five (rule : Nat → Nat → Option (Nat × Nat))
    (bounds : DOffsetBounds rule) {x y : Config}
    (hx : 5 ≤ x.n) (step : AffineStep rule x y) : x.n < y.n := by
  rcases step with ⟨r,k,c,hr,hn,hb,hy⟩
  rcases bounds with ⟨hb2,hb3,hb4⟩
  rcases hr with (hr2 | hr3 | hr4)
  · have hc := hb2 _ _ _ (by simpa [hr2] using hb)
    omega
  · have hc := hb3 _ _ _ (by simpa [hr3] using hb)
    omega
  · have hc := hb4 _ _ _ (by simpa [hr4] using hb)
    omega

theorem orbit_from_five_always_grows
    (rule : Nat → Nat → Option (Nat × Nat))
    (bounds : DOffsetBounds rule)
    (f : Nat → Config)
    (hstep : ∀ i, AffineStep rule (f i) (f (i+1)))
    (hfive : 5 ≤ (f 0).n) :
    ∀ i, (f i).n < (f (i+1)).n := by
  have hguard : ∀ i, 5 ≤ (f i).n := by
    intro i
    induction i with
    | zero => exact hfive
    | succ i ih =>
        have growth := affine_step_grows_from_five rule bounds ih (hstep i)
        omega
  intro i
  exact affine_step_grows_from_five rule bounds (hguard i) (hstep i)

theorem no_eventual_D_mode_suffix_period
    (rule : Nat → Nat → Option (Nat × Nat))
    (bounds : DOffsetBounds rule)
    (f : Nat → Config)
    (hstep : ∀ i, AffineStep rule (f i) (f (i+1)))
    (hfive : 5 ≤ (f 0).n)
    (a p : Nat) (hp : 0 < p)
    (hperiod : ∀ i, a ≤ i →
      (f i).suffix = (f (i+p)).suffix ∧
      (f i).n % 3 = (f (i+p)).n % 3) : False := by
  exact no_eventually_periodic_mode_and_suffix rule f hstep
    (orbit_from_five_always_grows rule bounds f hstep hfive)
    a p hp hperiod

#print axioms affine_step_grows_from_five
#print axioms orbit_from_five_always_grows
#print axioms no_eventual_D_mode_suffix_period
end BB6.Agent39
