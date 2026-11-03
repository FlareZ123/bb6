import Agent39DShadow

namespace BB6.Agent39

/-!
For a deterministic affine return decoder, a strictly increasing actual orbit
cannot eventually repeat its exact suffix together with the unary count's
residue modulo three. The finite-state periodicity claim is strictly stronger
than mere recurrent suffixes and does not establish nonhalting.
-/
theorem pair_matched_of_same_mode
    (rule : Nat → Nat → Option (Nat × Nat))
    {x x' y y' : Config}
    (h : AffineStep rule x y) (h' : AffineStep rule x' y')
    (hs : x.suffix = x'.suffix)
    (hr : x.n % 3 = x'.n % 3) (horder : x.n ≤ x'.n) :
    MatchedStep rule x x' y y' := by
  rcases h with ⟨r,k,c,hrange,hx,hb,hy⟩
  rcases h' with ⟨r',l,c',hrange',hx',hb',hy'⟩
  have hreq : r=r' := by
    rcases hrange with (h2 | h3 | h4) <;>
      rcases hrange' with (h2' | h3' | h4') <;>
      omega
  subst r'
  have hcst : (c,y.suffix)=(c',y'.suffix) := by
    apply Option.some.inj
    calc
      some (c,y.suffix) = rule r x.suffix := hb.symm
      _ = rule r x'.suffix := by rw [hs]
      _ = some (c',y'.suffix) := hb'
  have hceq : c=c' := congrArg Prod.fst hcst
  have hteq : y.suffix=y'.suffix := congrArg Prod.snd hcst
  have hkl : k≤l := by omega
  refine ⟨r,k,l,c,y.suffix,hrange,hx,hx',hkl,hs,hb,hy,?_,rfl,hteq.symm⟩
  simpa [hceq] using hy'

theorem monotone_orbit_offset
    (f : Nat → Config) (hmono : ∀ i, (f i).n < (f (i+1)).n)
    (i p : Nat) : (f i).n ≤ (f (i+p)).n := by
  induction p with
  | zero => simp
  | succ p ih =>
      have hnext := hmono (i+p)
      have hle := Nat.le_trans ih (Nat.le_of_lt hnext)
      simpa [Nat.add_assoc] using hle

theorem strict_orbit_offset
    (f : Nat → Config) (hmono : ∀ i, (f i).n < (f (i+1)).n)
    (i p : Nat) (hp : 0 < p) : (f i).n < (f (i+p)).n := by
  cases p with
  | zero => omega
  | succ p =>
      have hle := monotone_orbit_offset f hmono i p
      have hnext := hmono (i+p)
      have hlt := Nat.lt_of_le_of_lt hle hnext
      simpa [Nat.add_assoc] using hlt

theorem all_periodic_pairs_match
    (rule : Nat → Nat → Option (Nat × Nat))
    (f : Nat → Config)
    (hstep : ∀ i, AffineStep rule (f i) (f (i+1)))
    (hmono : ∀ i, (f i).n < (f (i+1)).n)
    (a p : Nat)
    (hperiod : ∀ i, a ≤ i →
      (f i).suffix = (f (i+p)).suffix ∧
      (f i).n % 3 = (f (i+p)).n % 3)
    (k : Nat) (i : Nat) (hi : a ≤ i) :
    MatchedSteps rule k (f i) (f (i+p)) (f (i+k)) (f (i+p+k)) := by
  induction k generalizing i with
  | zero => simpa using (MatchedSteps.zero (f i) (f (i+p)))
  | succ k ih =>
      obtain ⟨hs,hr⟩ := hperiod i hi
      have hfirst := pair_matched_of_same_mode rule (hstep i) (hstep (i+p))
         hs hr (monotone_orbit_offset f hmono i p)
      have hrest := ih (i+1) (by omega)
      have hrest' : MatchedSteps rule k (f (i+1)) (f (i+p+1))
          (f (i+1+k)) (f (i+p+1+k)) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest
      have hpairs := MatchedSteps.succ hfirst hrest'
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpairs

theorem no_eventually_periodic_mode_and_suffix
    (rule : Nat → Nat → Option (Nat × Nat))
    (f : Nat → Config)
    (hstep : ∀ i, AffineStep rule (f i) (f (i+1)))
    (hmono : ∀ i, (f i).n < (f (i+1)).n)
    (a p : Nat) (hp : 0 < p)
    (hperiod : ∀ i, a ≤ i →
      (f i).suffix = (f (i+p)).suffix ∧
      (f i).n % 3 = (f (i+p)).n % 3) : False := by
  apply no_distinct_perpetual_matched_orbits rule (f a) (f (a+p))
    (strict_orbit_offset f hmono a p hp)
  intro k
  refine ⟨f (a+k),f (a+p+k),?_⟩
  exact all_periodic_pairs_match rule f hstep hmono a p hperiod k a (Nat.le_refl _)


#print axioms no_eventually_periodic_mode_and_suffix
end BB6.Agent39
