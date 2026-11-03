import EAllDoubleFirst
import BoundaryPadding

namespace BB6.Agent32PhysicalObs

open CryptidBoundary BB6.Padding BB6.BoundaryPadding

/-- A finite half-tape carries no 1 exactly when every physical cell
    in its infinite blank-extended interpretation is zero. -/
theorem allZero_iff_anyFalse (xs : List Bool) :
    (xs.any id) = false ↔ ∀ n, bitAt xs n = false := by
  induction xs with
  | nil =>
      constructor
      · intro _ n
        simp [bitAt]
      · intro _
        rfl
  | cons b bs ih =>
      cases b with
      | false =>
          constructor
          · intro h n
            cases n with
            | zero => rfl
            | succ n =>
                have hbs : (bs.any id) = false := by simpa using h
                exact ih.mp hbs n
          · intro h
            have hbs : ∀ n, bitAt bs n = false := by
              intro n
              exact h (n+1)
            simpa using ih.mpr hbs
      | true =>
          constructor
          · intro h
            simp at h
          · intro h
            have hf : true = false := by simpa [bitAt] using h 0
            cases hf

/-- Padding-equivalent half-tapes have identical physical blank status. -/
theorem blankLeft_congr (xs ys : List Bool) (h : TapeEq xs ys) :
    ((xs.any id)=false ↔ (ys.any id)=false) := by
  rw [allZero_iff_anyFalse, allZero_iff_anyFalse]
  constructor
  · intro hx n
    rw [←h n]
    exact hx n
  · intro hy n
    rw [h n]
    exact hy n

/-- A physical F/0 return is invariant under the repository's genuine
    infinite-blank tape observation equivalence, including far zero padding. -/
theorem physicalF0_congr {c d : Cfg} (h : ObsEq c d) :
    BB6.Agent32EDoubleFirst.PhysicalF0 c ↔
      BB6.Agent32EDoubleFirst.PhysicalF0 d := by
  have hl : TapeEq c.l d.l := h.1
  have hh : c.h = d.h := h.2.1
  have hs : c.st = d.st := h.2.2.2
  constructor
  · intro hp
    obtain ⟨hpst,hph,hpl⟩ := hp
    exact ⟨hs.symm.trans hpst,hh.symm.trans hph,
      (blankLeft_congr c.l d.l hl).mp hpl⟩
  · intro hp
    obtain ⟨hpst,hph,hpl⟩ := hp
    exact ⟨hs.trans hpst,hh.trans hph,
      (blankLeft_congr c.l d.l hl).mpr hpl⟩

/-- Strict physical first-return exclusion transfers along the
    source-certified bisimulation for every finite primitive time. -/
theorem noPhysical_congr (n : Nat) {c d : Cfg} (h : ObsEq c d) :
    BB6.Agent32EDoubleFirst.NoPhysical c n ↔
      BB6.Agent32EDoubleFirst.NoPhysical d n := by
  constructor
  · intro hc t ht hp
    exact hc t ht ((physicalF0_congr (source_congr t h)).mpr hp)
  · intro hd t ht hp
    exact hd t ht ((physicalF0_congr (source_congr t h)).mp hp)

#print axioms allZero_iff_anyFalse
#print axioms blankLeft_congr
#print axioms physicalF0_congr
#print axioms noPhysical_congr
end BB6.Agent32PhysicalObs
