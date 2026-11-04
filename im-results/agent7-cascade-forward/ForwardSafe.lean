import ForwardProof

namespace CascadeForwardCert

/-- Composable, strictly chronological finite path. The bad predicate is
    checked at every source vertex before the final endpoint. -/
inductive SafePath (R : Nat → Nat → Prop) (bad : Nat → Bool) : Nat → Nat → Prop where
  | done {a : Nat} : SafePath R bad a a
  | next {a b c : Nat} (hb : bad a = false) (he : R a b)
      (hr : SafePath R bad b c) : SafePath R bad a c

theorem SafePath.trans {R : Nat → Nat → Prop} {bad : Nat → Bool}
    {a b c : Nat} (h1 : SafePath R bad a b) (h2 : SafePath R bad b c) :
    SafePath R bad a c := by
  induction h1 with
  | done => exact h2
  | next hb he hr ih => exact SafePath.next hb he (ih h2)

theorem SafePath.excludes {R : Nat → Nat → Prop} {bad : Nat → Bool}
    (strict : ∀ h u, R h u → h < u)
    (functional : ∀ h u v, R h u → R h v → u = v)
    {a b cap x : Nat} (hclean : SafePath R bad a b)
    (hcap : cap < b) (hreach : Chain R a x) (htarget : x ≤ cap)
    (hbad : bad x = true) : False := by
  induction hclean generalizing x with
  | done =>
      have hlo := chain_lower strict hreach
      omega
  | @next a y b hb he hr ih =>
      rcases chain_split functional he hreach with heq | hx
      · subst x
        simp [hb] at hbad
      · exact ih hcap hx htarget hbad

/-- A kernel-checkable segment produces a reusable proof-carrying SafePath,
    so each chunk can be compiled once as a separate Lean module. -/
theorem segment_safe {R : Nat → Nat → Prop}
    (good : Nat → Edge → Bool)
    (good_sound : ∀ h e, good h e = true → R h e.u)
    (bad : Nat → Bool) (finish : Nat) :
    ∀ es h, segment good bad finish h es = true → SafePath R bad h finish := by
  intro es
  induction es with
  | nil =>
      intro h hs
      have he : h = finish := of_decide_eq_true
        (show decide (h=finish)=true by simpa [segment] using hs)
      subst h
      exact SafePath.done
  | cons e es ih =>
      intro h hs
      have hb : bad h = false := by
        by_cases hh : bad h = true
        · simp [segment, hh] at hs
        · cases hh2 : bad h <;> simp_all
      have hg : good h e = true := by
        by_cases hh : good h e = true
        · exact hh
        · cases hh2 : good h e <;> simp_all [segment]
      have ht : segment good bad finish e.u es = true := by
        simpa [segment,hb,hg] using hs
      exact SafePath.next hb (good_sound h e hg) (ih e.u ht)

/-- The prior source proof of ResetChain can be embedded in generic Chain. -/
theorem root_chain_embeds {s u : Nat} (hr : CascadeResetInverse.ResetChain s u) :
    Chain CascadeResetInverse.ResetParent s u := by
  induction hr with
  | root => exact Chain.root
  | append hr hp ih => exact Chain.append ih hp

/-- Generic all-time fatal exclusion from a composable certified first-reset
    prefix, without constructing or reducing its concatenated list. -/
theorem safePath_survivor_exclusion (N endHeight : Nat)
    (hs : SafePath CascadeResetInverse.ResetParent (badHeight N) 2 endHeight)
    (hc : CascadeManyShield.fatal N < endHeight)
    (n : Nat) (hn : 4 ≤ n) (hbound : n ≤ N)
    (hres : n%6=4 ∨ n%6=5) :
    ¬CascadeSweep.ReachC (2,0) (CascadeManyShield.fatal n,0) := by
  intro hr
  have hb : badHeight N (CascadeManyShield.fatal n)=true :=
    CascadeFastShield.badFast_hits N n hn hbound hres
  have hcap : CascadeManyShield.fatal n ≤ CascadeManyShield.fatal N :=
    CascadeFastShield.fatal_mono n N hbound
  have hchain : Chain CascadeResetInverse.ResetParent 2 (CascadeManyShield.fatal n) :=
    root_chain_embeds ((CascadeResetInverse.root_reset_chain_iff _).mp hr)
  exact SafePath.excludes CascadeResetInverse.reset_parent_strict
    parent_functional hs hc hchain hcap hb

#print axioms SafePath.excludes
#print axioms segment_safe
#print axioms safePath_survivor_exclusion
end CascadeForwardCert
