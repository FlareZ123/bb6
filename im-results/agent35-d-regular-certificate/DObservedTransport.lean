import DTransport

namespace DRegular

/-- Reusable transport across representations of the same physical tape.
    The relation R may be original equality or far-blank observational equality.
    The only Turing-machine-specific obligations are per-case hOne and
    a congruence proof for R under the raw transition semantics. -/
theorem transport_obs {Cfg : Type} (raw : Nat → Cfg → Cfg)
    (sec : L → Cfg) (R : Cfg → Cfg → Prop)
    (hzero : ∀ c, raw 0 c = c)
    (hadd : ∀ p q c, raw (p+q) c = raw q (raw p c))
    (hrefl : ∀ c, R c c)
    (htrans : ∀ x y z, R x y → R y z → R x z)
    (hcongr : ∀ n x y, R x y → R (raw n x) (raw n y))
    (hOne : ∀ s t, Canon s → next s = some t →
      R (raw (duration s) (sec s)) (sec t))
    (n : Nat) (s t : L) (hc : Canon s)
    (hrun : run n s = some t) :
    R (raw (accumulated n s) (sec s)) (sec t) := by
  induction n generalizing s with
  | zero =>
    simp only [run] at hrun
    cases hrun
    rw [accumulated, hzero]
    exact hrefl _
  | succ n ih =>
    cases hs : next s with
    | none => simp [run, hs] at hrun
    | some u =>
      have hu : run n u = some t := by simpa [run, hs] using hrun
      have hcu : Canon u := next_canon s u hc hs
      have hr := hOne s u hc hs
      have ht := ih u hcu hu
      rw [show accumulated (n+1) s = duration s + accumulated n u
        by simp [accumulated, hs], hadd]
      exact htrans _ _ _ (hcongr (accumulated n u) _ _ hr) ht

/-- All first 1711 modeled seed5 returns can be promoted through any
    sufficiently certified original-machine physical congruence. -/
theorem seed5_transport_obs {Cfg : Type} (raw : Nat → Cfg → Cfg)
    (sec : L → Cfg) (R : Cfg → Cfg → Prop)
    (hzero : ∀ c, raw 0 c = c)
    (hadd : ∀ p q c, raw (p+q) c = raw q (raw p c))
    (hrefl : ∀ c, R c c)
    (htrans : ∀ x y z, R x y → R y z → R x z)
    (hcongr : ∀ n x y, R x y → R (raw n x) (raw n y))
    (hOne : ∀ s t, Canon s → next s = some t →
      R (raw (duration s) (sec s)) (sec t)) :
    R (raw (accumulated 1711 seed5) (sec seed5)) (sec terminal5) := by
  have h : run 1711 seed5 = some terminal5 := by
    have hs := seed5_survives_1711
    cases e : run 1711 seed5 with
    | none => simp [e] at hs
    | some s => simp [terminal5, e]
  have hc : Canon seed5 := by simp [Canon, seed5]
  exact transport_obs raw sec R hzero hadd hrefl htrans hcongr hOne
    1711 seed5 terminal5 hc h

#print axioms transport_obs
#print axioms seed5_transport_obs

end DRegular
