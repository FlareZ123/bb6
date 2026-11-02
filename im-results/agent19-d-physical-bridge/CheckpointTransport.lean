import ExactTime

namespace BB6.Agent19.Physical

/-- The proof-carrying finite tape has no hidden degrees of freedom once
    the complete finite tape and the physical head offset are fixed. -/
theorem safeCfg_ext (c d : SafeCfg)
    (htape : c.data = d.data) (hhead : c.offset = d.offset) : c = d := by
  cases c with
  | mk a x ha =>
    cases d with
    | mk b y hb =>
      cases htape
      cases hhead
      rfl

/-- Complete semantic transport of ANY nonhalting, original-source exact
    primitive-time checkpoint to a real infinite-tape configuration.
    The resulting physical head offset exists and is exact. -/
theorem source_live_checkpoint (n : Nat) (c d : CryptidBoundary.Cfg)
    (hc : c.st < 6) (hd : d.st < 6)
    (hr : CryptidBoundary.run n c = d) (offset : Int) :
    ∃ nextOffset : Int,
      BB6.Portfolio.run BB6.Portfolio.D0 n
        (some (realize (boundarySafe c hc offset))) =
      some (realize (boundarySafe d hd nextOffset)) := by
  have hsrc : BB6.Padding.run BB6.BoundaryPadding.delta n
      (BB6.BoundaryPadding.represent c) = BB6.BoundaryPadding.represent d := by
    have h := BB6.BoundaryPadding.source_run n c
    rw [hr] at h
    exact h.symm
  have hrel := rel_run n (some (boundarySafe c hc offset))
    (BB6.BoundaryPadding.represent c) rfl
  rw [hsrc] at hrel
  cases hf : runFinite n (some (boundarySafe c hc offset)) with
  | none =>
    simp only [hf,RunRel] at hrel
    change (BB6.BoundaryPadding.represent d).state = 6 at hrel
    change d.st = 6 at hrel
    omega
  | some z =>
    have hdrep : z.data = BB6.BoundaryPadding.represent d := by
      simpa only [hf,RunRel] using hrel
    have hrz : BB6.Portfolio.run BB6.Portfolio.D0 n
      (some (realize (boundarySafe c hc offset))) = some (realize z) := by
      simpa only [hf,Option.map_some] using
        (run_semiconjugacy n (some (boundarySafe c hc offset)))
    have hz : z = boundarySafe d hd z.offset := by
      apply safeCfg_ext
      · simpa [boundarySafe] using hdrep
      · rfl
    exact ⟨z.offset, hrz.trans (congrArg (fun x : SafeCfg => some (realize x)) hz)⟩

/-- Physical checkpoint transportation is invariant under initial-head
    coordinate translation: every source theorem can be lifted from any
    physical tape origin without needing to inspect intermediate states. -/
theorem source_live_checkpoint_zero (n : Nat) (c d : CryptidBoundary.Cfg)
    (hc : c.st < 6) (hd : d.st < 6)
    (hr : CryptidBoundary.run n c = d) :
    ∃ nextOffset : Int,
      BB6.Portfolio.run BB6.Portfolio.D0 n
        (some (realize (boundarySafe c hc 0))) =
      some (realize (boundarySafe d hd nextOffset)) :=
  source_live_checkpoint n c d hc hd hr 0

#print axioms safeCfg_ext
#print axioms source_live_checkpoint
#print axioms source_live_checkpoint_zero
end BB6.Agent19.Physical
