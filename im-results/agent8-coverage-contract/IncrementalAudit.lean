import FrontierMass

namespace BB6Coverage

/-- Build the graft while proving its *exact* open-set semantics: a completion
of the current leaf remains open precisely when it fails to match the source
cylinder. The recursion branches only at source-fixed slots not already fixed
by the leaf; a mismatch is retained as an unresolved child. -/
private noncomputable def graftFromSlotsWithOpenIff {good : Machine → Prop}
    (src : PartialMachine) (cert : Cover good src)
    (p : PartialMachine) (remaining : List Slot)
    (hprocessed : ∀ s, s ∉ remaining → ∀ t, src s = some t → p s = some t) :
    { audit : FrontierAudit good p //
      ∀ m, compatible p m →
        (audit.open m ↔ ¬ compatible src m) } := by
  classical
  induction remaining generalizing p with
  | nil =>
      refine ⟨.certified p (.leaf p (by
        intro full hm
        apply cert.sound full
        intro s t ht
        exact hm s t (hprocessed s (by simp) t ht))), ?_⟩
      intro m hm
      constructor
      · intro hopen
        exact False.elim hopen
      · intro hnot
        have hsrc : compatible src m := by
          intro s t ht
          exact hm s t (hprocessed s (by simp) t ht)
        exact (hnot hsrc).elim
  | cons slot rest ih =>
      by_cases hsrc : src slot = none
      · have hproc : ∀ s, s ∉ rest → ∀ t, src s = some t → p s = some t := by
          intro s hs t ht
          by_cases heq : s = slot
          · subst s
            rw [hsrc] at ht
            contradiction
          · exact hprocessed s (by simp [heq, hs]) t ht
        exact ih p hproc
      · cases hst : src slot with
        | none => contradiction
        | some t =>
          cases hp : p slot with
          | none =>
              have hproc : ∀ s, s ∉ rest → ∀ v, src s = some v →
                  refine p slot t s = some v := by
                intro s hsNot v hv
                by_cases heq : s = slot
                · subst s
                  have htv : t = v := Option.some.inj (hst.symm.trans hv)
                  subst v
                  simp [refine]
                · have hOld := hprocessed s (by simp [heq, hsNot]) v hv
                  simpa [refine, heq] using hOld
              let child := ih (refine p slot t) hproc
              refine ⟨.branch p slot hp (fun u hu => by
                by_cases huEq : u = t
                · subst u
                  exact child.1
                · exact .unresolved (refine p slot u)), ?_⟩
              intro m hm
              constructor
              · intro hopen hsrcm
                have hmt : m slot = t := hsrcm slot t hst
                cases hmt
                have hchild : compatible (refine p slot (m slot)) m := by
                  rw [compatible_refine_iff p m slot hp (m slot)]
                  exact ⟨hm, rfl⟩
                have hchildOpen : child.1.open m := by
                  simpa [FrontierAudit.open] using hopen
                exact (child.2 m hchild).mp hchildOpen hsrcm
              · intro hnot
                by_cases hu : m slot = t
                · cases hu
                  have hchild : compatible (refine p slot (m slot)) m := by
                    rw [compatible_refine_iff p m slot hp (m slot)]
                    exact ⟨hm, rfl⟩
                  have hchildOpen : child.1.open m :=
                    (child.2 m hchild).mpr hnot
                  simpa [FrontierAudit.open] using hchildOpen
                · simp [FrontierAudit.open, hu]
          | some u =>
              by_cases huEq : u = t
              · have hproc : ∀ s, s ∉ rest → ∀ v, src s = some v → p s = some v := by
                  intro s hsNot v hv
                  by_cases heq : s = slot
                  · subst s
                    have htv : t = v := Option.some.inj (hst.symm.trans hv)
                    subst v
                    simpa [huEq] using hp
                  · exact hprocessed s (by simp [heq, hsNot]) v hv
                exact ih p hproc
              · refine ⟨.unresolved p, ?_⟩
                intro m hm
                constructor
                · intro _ hsrcm
                  have hmu : m slot = u := hm slot u hp
                  have hmt : m slot = t := hsrcm slot t hst
                  exact huEq (hmu.symm.trans hmt)
                · intro _
                  trivial

/-- The proof-carrying audit component of `graftFromSlotsWithOpenIff`. -/
private noncomputable def graftFromSlots {good : Machine → Prop}
    (src : PartialMachine) (cert : Cover good src)
    (p : PartialMachine) (remaining : List Slot)
    (hprocessed : ∀ s, s ∉ remaining → ∀ t, src s = some t → p s = some t) :
    FrontierAudit good p :=
  (graftFromSlotsWithOpenIff src cert p remaining hprocessed).1

/-- Attach an authenticated partial-cylinder certificate to a fully open
leaf, branching on source-assigned slots not already fixed by that leaf. -/
noncomputable def graftCertificate {good : Machine → Prop}
    (p src : PartialMachine) (cert : Cover good src) : FrontierAudit good p :=
  graftFromSlots src cert p auditSlots (by
    intro s hs t hsrc
    exact False.elim (hs (auditSlots_complete s)))

/-- Proof-preserving augmentation of an existing arbitrary frontier with a
second independently established cylinder. Already-certified nodes survive,
and only unresolved leaves acquire 25-way source-compatible branches. -/
noncomputable def addCertificate {good : Machine → Prop} {p : PartialMachine}
    (audit : FrontierAudit good p) (src : PartialMachine)
    (cert : Cover good src) : FrontierAudit good p := by
  induction audit with
  | certified p proof => exact .certified p proof
  | unresolved p => exact graftCertificate p src cert
  | branch p slot fresh children ih =>
      exact .branch p slot fresh (fun t ht => ih t ht)

/-- Exact open-set characterization for a single grafted leaf. This proves
both directions: source-compatible completions are closed, and every
source-incompatible completion stays explicitly unresolved. -/
theorem graftCertificate_open_iff {good : Machine → Prop}
    (p src : PartialMachine) (cert : Cover good src) (m : Machine)
    (hm : compatible p m) :
    (graftCertificate p src cert).open m ↔ ¬ compatible src m := by
  unfold graftCertificate
  exact (graftFromSlotsWithOpenIff src cert p auditSlots
    (by
      intro s hs t hsrc
      exact False.elim (hs (auditSlots_complete s)))).2 m hm

theorem graftCertificate_closes_source {good : Machine → Prop}
    (p src : PartialMachine) (cert : Cover good src) :
    ∀ m, compatible p m → compatible src m →
      ¬ (graftCertificate p src cert).open m := by
  intro m hm hs hopen
  exact (graftCertificate_open_iff p src cert m hm).mp hopen hs

/-- Exact semantics of `addCertificate`: it removes precisely the machines
that both belonged to the old open frontier and match the new source
certificate. No source-incompatible open machine is silently discarded. -/
theorem addCertificate_open_iff {good : Machine → Prop}
    {p : PartialMachine} (audit : FrontierAudit good p)
    (src : PartialMachine) (cert : Cover good src) (m : Machine)
    (hm : compatible p m) :
    (addCertificate audit src cert).open m ↔
      audit.open m ∧ ¬ compatible src m := by
  induction audit with
  | certified p proof =>
      simp [addCertificate, FrontierAudit.open]
  | unresolved p =>
      simpa [addCertificate, FrontierAudit.open] using
        (graftCertificate_open_iff p src cert m hm)
  | branch p slot fresh children ih =>
      have hchild : compatible (refine p slot (m slot)) m :=
        compatible_refine p m slot hm
      simpa [addCertificate, FrontierAudit.open] using
        (ih (m slot) (choices_complete (m slot)) hchild)

/-- Source-compatible machines are never left in an open terminal after a
certificate is grafted into an audit. -/
theorem addCertificate_closes_source {good : Machine → Prop}
    {p : PartialMachine} (audit : FrontierAudit good p)
    (src : PartialMachine) (cert : Cover good src) :
    ∀ m, compatible p m → compatible src m →
      ¬ (addCertificate audit src cert).open m := by
  intro m hm hs hopen
  exact ((addCertificate_open_iff audit src cert m hm).mp hopen).2 hs

#print axioms graftCertificate_closes_source
#print axioms addCertificate_closes_source
#print axioms graftCertificate_open_iff
#print axioms addCertificate_open_iff
#print axioms graftCertificate
#print axioms addCertificate
end BB6Coverage
