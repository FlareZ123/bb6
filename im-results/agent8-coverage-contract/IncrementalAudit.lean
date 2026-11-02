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

#print axioms graftCertificate
#print axioms addCertificate
end BB6Coverage
