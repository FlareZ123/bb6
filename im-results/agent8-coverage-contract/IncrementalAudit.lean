import FrontierMass

namespace BB6Coverage

/-- Attach an authenticated partial-cylinder certificate to a fully open
leaf, branching on source-assigned slots not already fixed by that leaf. -/
private noncomputable def graftFromSlots {good : Machine → Prop}
    (src : PartialMachine) (cert : Cover good src)
    (p : PartialMachine) (remaining : List Slot)
    (hprocessed : ∀ s, s ∉ remaining → ∀ t, src s = some t → p s = some t) :
    FrontierAudit good p := by
  induction remaining generalizing p with
  | nil =>
      apply FrontierAudit.certified p
      apply Cover.leaf p
      intro full hm
      apply cert.sound full
      intro s t ht
      exact hm s t (hprocessed s (by simp) t ht)
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
      · cases ht : src slot with
        | none => contradiction
        | some t =>
            cases hp : p slot with
            | none =>
                apply FrontierAudit.branch p slot hp
                intro u hu
                by_cases huEq : u = t
                · subst u
                  have hproc : ∀ s, s ∉ rest → ∀ v, src s = some v →
                      refine p slot t s = some v := by
                    intro s hs v hv
                    by_cases heq : s = slot
                    · subst s
                      have heqt : t = v := Option.some.inj (ht.symm.trans hv)
                      subst v
                      simp [refine]
                    · have hOld := hprocessed s (by simp [heq, hs]) v hv
                      simpa [refine, heq] using hOld
                  exact ih (refine p slot t) hproc
                · exact FrontierAudit.unresolved (refine p slot u)
            | some u =>
                by_cases huEq : u = t
                · subst u
                  have hproc : ∀ s, s ∉ rest → ∀ v, src s = some v → p s = some v := by
                    intro s hs v hv
                    by_cases heq : s = slot
                    · subst s
                      have heqt : t = v := Option.some.inj (ht.symm.trans hv)
                      subst v
                      exact hp
                    · exact hprocessed s (by simp [heq, hs]) v hv
                  exact ih p hproc
                · exact FrontierAudit.unresolved p

/-- Every inserted proof remains valid for all compatible full tables;
unmatched alternatives stay explicitly unresolved. -/
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

/-- Every machine compatible with the inserted source cylinder follows the
unique matching branch at each source-fixed slot and reaches a certified
leaf. This is the closure property needed to interpret `addCertificate`
as an actual reduction of the open frontier, not merely as a proof-preserving
tree constructor. -/
private theorem graftFromSlots_closes_source {good : Machine → Prop}
    (src : PartialMachine) (cert : Cover good src) :
    ∀ (p : PartialMachine) (remaining : List Slot)
      (hprocessed : ∀ s, s ∉ remaining → ∀ t, src s = some t → p s = some t)
      (m : Machine), compatible p m → compatible src m →
      ¬ (graftFromSlots src cert p remaining hprocessed).open m := by
  intro p remaining
  induction remaining generalizing p with
  | nil =>
      intro hprocessed m hm hs
      simp [graftFromSlots, FrontierAudit.open]
  | cons slot rest ih =>
      intro hprocessed m hm hs
      by_cases hsrc : src slot = none
      · have hproc : ∀ s, s ∉ rest → ∀ t, src s = some t → p s = some t := by
          intro s hsNot t ht
          by_cases heq : s = slot
          · subst s
            rw [hsrc] at ht
            contradiction
          · exact hprocessed s (by simp [heq, hsNot]) t ht
        have hno := ih p hproc m hm hs
        intro hopen
        exact hno (by simpa [graftFromSlots, hsrc] using hopen)
      · cases hst : src slot with
        | none => contradiction
        | some t =>
          cases hpSlot : p slot with
          | none =>
              have hmt : m slot = t := hs slot t hst
              have hchild : compatible (refine p slot t) m := by
                rw [compatible_refine_iff p m slot hpSlot t]
                exact ⟨hm, hmt⟩
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
              have hno := ih (refine p slot t) hproc m hchild hs
              intro hopen
              apply hno
              simpa [graftFromSlots, hsrc, hst, hpSlot,
                FrontierAudit.open, hmt] using hopen
          | some u =>
              have hmu : m slot = u := hm slot u hpSlot
              have hmt : m slot = t := hs slot t hst
              have hut : u = t := hmu.symm.trans hmt
              subst u
              have hproc : ∀ s, s ∉ rest → ∀ v, src s = some v → p s = some v := by
                intro s hsNot v hv
                by_cases heq : s = slot
                · subst s
                  have htv : t = v := Option.some.inj (hst.symm.trans hv)
                  subst v
                  exact hpSlot
                · exact hprocessed s (by simp [heq, hsNot]) v hv
              have hno := ih p hproc m hm hs
              intro hopen
              apply hno
              simpa [graftFromSlots, hsrc, hst, hpSlot,
                FrontierAudit.open] using hopen

/-- Source-compatible machines are never left in an open terminal after a
certificate is grafted into an audit. Unmatched source outcomes remain
explicitly unresolved by `graftFromSlots`. -/
theorem graftCertificate_closes_source {good : Machine → Prop}
    (p src : PartialMachine) (cert : Cover good src) :
    ∀ m, compatible p m → compatible src m →
      ¬ (graftCertificate p src cert).open m := by
  intro m hm hs
  unfold graftCertificate
  exact graftFromSlots_closes_source src cert p auditSlots
    (by
      intro s hnot t hsrc
      exact False.elim (hnot (auditSlots_complete s)))
    m hm hs

/-- The generic `addCertificate` operation closes every source-compatible
machine wherever the source cylinder meets an unresolved leaf of the audit. -/
theorem addCertificate_closes_source {good : Machine → Prop}
    {p : PartialMachine} (audit : FrontierAudit good p)
    (src : PartialMachine) (cert : Cover good src) :
    ∀ m, compatible p m → compatible src m →
      ¬ (addCertificate audit src cert).open m := by
  induction audit with
  | certified p proof =>
      intro m hm hs
      simp [addCertificate, FrontierAudit.open]
  | unresolved p =>
      intro m hm hs
      exact graftCertificate_closes_source p src cert m hm hs
  | branch p slot fresh children ih =>
      intro m hm hs
      have hchild : compatible (refine p slot (m slot)) m :=
        compatible_refine p m slot hm
      have hno := ih (m slot) (choices_complete (m slot)) m hchild hs
      intro hopen
      apply hno
      simpa [addCertificate, FrontierAudit.open] using hopen

#print axioms graftCertificate_closes_source
#print axioms addCertificate_closes_source

#print axioms graftCertificate
#print axioms addCertificate
end BB6Coverage
