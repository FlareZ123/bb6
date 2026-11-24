import CapCanonicalParent

namespace CapSieve

theorem canonical_return_grows {k q j v : Nat} (hc : CanonQ k q)
    (he : (signedEvent k q).2=some (j,v)) : k<j := by
  have hb := signed_event_band k q
  have hr := signed_event_return (pos_valid hc.1) he
  omega

/-- Canonical positive-return reachability. -/
inductive CReach : Nat → Nat → Nat → Nat → Prop where
  | refl {k q : Nat} : CanonQ k q → CReach k q k q
  | tail {k q j v b u : Nat} : CReach k q j v →
      (signedEvent j v).2=some (b,u) → CReach k q b u

theorem c_reach_valid {k q j v : Nat} (h : CReach k q j v) :
    CanonQ k q ∧ CanonQ j v ∧ k≤j := by
  induction h with
  | refl h => exact ⟨h,h,by omega⟩
  | tail h e ih =>
    have hv := pos_valid ih.2.1.1
    have hcan := signed_event_canonical hv e
    have hb := canonical_return_grows ih.2.1 e
    exact ⟨ih.1,hcan,by omega⟩

theorem c_reach_prepend {k q j v b u : Nat} (hc : CanonQ k q)
    (he : (signedEvent k q).2=some (j,v)) (hr : CReach j v b u) :
    CReach k q b u := by
  induction hr with
  | refl => exact .tail (.refl hc) he
  | tail _ e ih => exact .tail ih e

theorem c_reach_event_band {k q j v : Nat} (h : CReach k q j v) :
    (signedEvent k q).1≤j ∨ (j=k ∧ v=q) := by
  induction h with
  | refl => exact Or.inr ⟨rfl,rfl⟩
  | tail hr he ih =>
    have hv := (c_reach_valid hr).2.1
    rcases ih with h|⟨rfl,rfl⟩
    · have hg := canonical_return_grows hv he
      exact Or.inl (by omega)
    · have hg := signed_event_return (pos_valid hv.1) he
      exact Or.inl (by omega)

theorem c_reach_first {k q j v b u : Nat}
    (hcan : CanonQ j v) (he : (signedEvent k q).2=some (j,v))
    (hr : CReach k q b u) :
    (b=k ∧ u=q) ∨ CReach j v b u := by
  induction hr with
  | refl => exact Or.inl ⟨rfl,rfl⟩
  | tail hr e ih =>
    rcases ih with ⟨rfl,rfl⟩|h
    · rw [he] at e
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj e)
      exact Or.inr (.refl hcan)
    · exact Or.inr (.tail h e)

/-- Exact connection between signedHaltBy and the canonical graph. -/
theorem signed_halt_canonical {limit k q : Nat} (hc : CanonQ k q) :
    signedHaltBy limit k q=true ↔ ∃ j v, CReach k q j v ∧
      (signedEvent j v).1≤limit ∧ (signedEvent j v).2=none := by
  rw [signedHaltBy]
  have hb := signed_event_band k q
  by_cases hl : (signedEvent k q).1>limit
  · rw [if_pos hl]
    constructor
    · intro h; contradiction
    · rintro ⟨j,v,hr,hlim,ht⟩
      have h := c_reach_event_band hr
      have hbj := signed_event_band j v
      rcases h with h|⟨rfl,rfl⟩ <;> omega
  · rw [if_neg hl]
    cases he : (signedEvent k q).2 with
    | none =>
      constructor
      · intro _
        exact ⟨k,q,.refl hc,by omega,he⟩
      · intro _; rfl
    | some z =>
      obtain ⟨j,v⟩ := z
      have hv := pos_valid hc.1
      have hret := signed_event_return hv he
      have hj : k<j := by omega
      have hcan := signed_event_canonical hv he
      change (if k<j then signedHaltBy limit j v else false)=true ↔ _
      rw [if_pos hj,signed_halt_canonical hcan]
      constructor
      · rintro ⟨b,u,hr,hlim,ht⟩
        exact ⟨b,u,c_reach_prepend hc he hr,hlim,ht⟩
      · rintro ⟨b,u,hr,hlim,ht⟩
        have h := c_reach_first hcan he hr
        rcases h with ⟨rfl,rfl⟩|h
        · rw [he] at ht; contradiction
        · exact ⟨b,u,h,hlim,ht⟩
termination_by limit+1-k
decreasing_by omega

/-- Trace a canonical node backwards until band five or below. -/
def anchorOf (j q : Nat) : Option (Nat × Nat) :=
  if j≤5 then some (j,q)
  else match canonicalParent j q with
       | none => none
       | some (k,v) => if k<j then anchorOf k v else none
termination_by j
decreasing_by omega

theorem anchor_of_iff {j q a : Nat} (hc : CanonQ j q) (ha : CanonQ 5 a) :
    anchorOf j q=some (5,a) ↔ CReach 5 a j q := by
  rw [anchorOf]
  by_cases hj : j≤5
  · rw [if_pos hj]
    constructor
    · intro h
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact .refl ha
    · intro h
      cases h with
      | refl => rfl
      | tail hr he =>
        have hv := c_reach_valid hr
        have hs := canonical_return_grows hv.2.1 he
        omega
  · rw [if_neg hj]
    cases hp : canonicalParent j q with
    | none =>
      constructor
      · intro h; contradiction
      · intro h
        cases h with
        | refl => omega
        | tail hr he =>
          have hv := (c_reach_valid hr).2.1
          rw [canonical_parent_complete (by omega) hv he] at hp
          contradiction
    | some z =>
      obtain ⟨k,v⟩ := z
      obtain ⟨hv,he⟩ := canonical_parent_sound (by omega) hc hp
      have hb := signed_event_band k v
      have hs := signed_event_return (pos_valid hv.1) he
      have hk : k<j := by omega
      change (if k<j then anchorOf k v else none)=some (5,a) ↔ _
      rw [if_pos hk,anchor_of_iff hv ha]
      constructor
      · intro h
        exact .tail h he
      · intro h
        cases h with
        | refl => omega
        | tail hr e =>
          have hv' := (c_reach_valid hr).2.1
          have hp' := canonical_parent_complete (by omega) hv' e
          rw [hp] at hp'
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj hp')
          exact hr
termination_by j
decreasing_by omega

#print axioms c_reach_valid
#print axioms signed_halt_canonical
#print axioms anchor_of_iff
end CapSieve
