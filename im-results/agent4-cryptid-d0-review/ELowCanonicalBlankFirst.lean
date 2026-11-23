import Lean.Elab.Tactic.Omega
import ELowPhysicalFirstReturnRepair
import BoundaryPadding

/-!
# E low-row strict first return on the canonical, implicit-blank tape

TapeEq equates finite half tapes modulo trailing zero padding.  A literal
left-list equality with [] is not observationally invariant, but the stronger
physical proposition `TapeEq c.l []` is invariant.  This file strengthens
the corrected E-pairs first-return argument to exclude every early F/0
state with physically blank left half-plane.  It then transports the theorem
from the explicit final zero to the original unpadded source section.

Authoring status: candidate Lean proof; subject to real compiler and axiom audit.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

namespace BB6.CryptidELowCanonicalFirst

open CryptidBoundary
open BB6.Padding (TapeEq tapeEq_trans tapeEq_symm bitAt)
open BB6.BoundaryPadding
open BB6.CryptidPrefixFirstReturn
open BB6.CryptidE111FirstReturn
open BB6.CryptidFirstReturn
open BB6.CryptidELowPhysicalRepair

/-- Exactly F scanning zero, with no *physical* ones anywhere to its left.
This is invariant under blank-padding congruence, unlike `c.l = []`. -/
def BlankLeftF (c : Cfg) : Prop :=
  c.st = 5 ∧ c.h = false ∧ TapeEq c.l []

def NoBlankF (c : Cfg) (n : Nat) : Prop :=
  ∀ t, t < n → ¬ BlankLeftF (run t c)

/-- Blank-left F/0 is preserved in both directions under tape observation. -/
theorem blankLeftF_congr {c d : Cfg} (h : ObsEq c d) :
    BlankLeftF c ↔ BlankLeftF d := by
  change TapeEq c.l d.l ∧ c.h = d.h ∧
    TapeEq c.r d.r ∧ c.st = d.st at h
  rcases h with ⟨hl, hh, hr, hs⟩
  constructor
  · rintro ⟨hcst, hch, hcl⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [← hs]; exact hcst
    · rw [← hh]; exact hch
    · exact tapeEq_trans (tapeEq_symm hl) hcl
  · rintro ⟨hdst, hdh, hdl⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [hs]; exact hdst
    · rw [hh]; exact hdh
    · exact tapeEq_trans hl hdl

private theorem noF_to_noBlank (c : Cfg) (n : Nat)
    (hf : NoF c n) : NoBlankF c n := by
  intro t ht hb
  exact hf t ht hb.1

private theorem appendNoBlank (c d : Cfg) (a b : Nat)
    (hc : NoBlankF c a) (he : run a c = d) (hd : NoBlankF d b) :
    NoBlankF c (a+b) := by
  intro t ht
  by_cases hs : t < a
  · exact hc t hs
  · have heq : t=a+(t-a) := by omega
    rw [heq, run_add, he]
    exact hd (t-a) (by omega)

/-- A C/1 -> D/1 -> F intermediate visit has a 1 immediately to its
left. This holds for every m and every continuation. -/
private theorem cBase_noBlank (m : Nat) (ys : List Bool) :
    NoBlankF (⟨pairs (m+2) ++ [true,true], true, ys, 2⟩ : Cfg) 4 := by
  intro t ht hb
  have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  · simp [BlankLeftF,run] at hb
  · simp [BlankLeftF,run,step,goL,goR,pairs] at hb
  · have hbit : bitAt
        (run 2 (⟨pairs (m+2) ++ [true,true], true, ys, 2⟩ : Cfg)).l 0 =
        true := by
        simp [run,step,goL,goR,pairs,bitAt]
    have hz := hb.2.2 0
    rw [hbit] at hz
    simpa [bitAt] using hz
  · simp [BlankLeftF,run,step,goL,goR,pairs] at hb

/-- All E-pairs steps before the final B sweep have no F/0 event with
a physically empty left half-plane (including arbitrary blank padding). -/
theorem ePairs_toB_noBlank (m q : Nat) (ys : List Bool) :
    NoBlankF (ePairs m q ys) (4*q+12) := by
  let L : List Bool := pairs (m+2) ++ [true,true]
  have hb : NoBlankF
      (⟨L, true, List.replicate (2*(q+1)) true ++ (true::ys), 2⟩ : Cfg) 4 := by
    dsimp [L]
    exact cBase_noBlank m _
  have hc : NoBlankF (cWalk (q+1) L (true::ys))
      (2*(q+1)+4) :=
    appendNoBlank
      (cWalk (q+1) L (true::ys))
      (⟨L, true, List.replicate (2*(q+1)) true ++ (true::ys), 2⟩ : Cfg)
      (2*(q+1)) 4
      (noF_to_noBlank _ _ (cWalk_noF (q+1) L (true::ys)))
      (cWalk_run (q+1) L (true::ys))
      hb
  have ha : NoBlankF (aCloseStart (q+1) m ys)
      (2+(2*(q+1)+4)) :=
    appendNoBlank
      (aCloseStart (q+1) m ys)
      (cWalk (q+1) L (true::ys))
      2 (2*(q+1)+4)
      (noF_to_noBlank _ _ (aCloseStart_noF (q+1) m ys))
      (aClose_two (q+1) m ys)
      hc
  have hs : NoBlankF
      (scanStart (q+1) L (false::ys))
      (2*(q+1)+(2+(2*(q+1)+4))) := by
    have hscan : NoF (scanStart (q+1) L (false::ys))
        (2*(q+1)) := scanner_noF (q+1) L (false::ys)
    have he : run (2*(q+1)) (scanStart (q+1) L (false::ys)) =
        aCloseStart (q+1) m ys := by
      rw [scan_run]
      rfl
    exact appendNoBlank _ _ (2*(q+1)) (2+(2*(q+1)+4))
      (noF_to_noBlank _ _ hscan) he ha
  have he : NoBlankF (ePairs m q ys)
      (2+(2*(q+1)+(2+(2*(q+1)+4)))) :=
    appendNoBlank
      (ePairs m q ys)
      (scanStart (q+1) L (false::ys))
      2 (2*(q+1)+(2+(2*(q+1)+4)))
      (noF_to_noBlank _ _ (ePairs_start_noF m q ys))
      (ePairs_two m q ys)
      hs
  have htime :
      2+(2*(q+1)+(2+(2*(q+1)+4)))=4*q+12 := by omega
  simpa only [htime] using he

theorem ePairs_no_early_blank (m q : Nat) (ys : List Bool) :
    NoBlankF (ePairs m q ys) (2*m+4*q+15) := by
  have htime : 2*m+4*q+15=(4*q+12)+(2*m+3) := by omega
  rw [htime]
  have htail : NoBlankF
      (sweepB m (false::List.replicate (2*q+6) true ++ ys))
      (2*m+3) := by
    intro t ht hb
    exact (sweepB_firstF m
      (false::List.replicate (2*q+6) true ++ ys) t ht) hb.1
  exact appendNoBlank
    (ePairs m q ys)
    (sweepB m (false::List.replicate (2*q+6) true ++ ys))
    (4*q+12) (2*m+3)
    (ePairs_toB_noBlank m q ys)
    (ePairs_toB m q ys)
    htail

theorem full_E_pairs_no_early_blank (k q : Nat) :
    let n := 12*k*k+49*k+50+4*q
    let source := init (List.replicate (3*k+2) true ++
      false :: (pairs q ++ [false]))
    ∀ t, 0<t → t<n → ¬BlankLeftF (run t source) := by
  dsimp
  intro t hpos ht hb
  let preCost : Nat := 12*k*k+41*k+33
  by_cases hpref : t<preCost
  · exact (prefixE_positive_noF k (pairs q ++ [false])
      t hpos hpref) hb.1
  · have heq : t=preCost+(t-preCost) := by omega
    rw [heq,run_add,prefix_E] at hb
    change BlankLeftF (run (t-preCost) (ePairs (4*k+1) q [])) at hb
    exact (ePairs_no_early_blank (4*k+1) q [])
      (t-preCost) (by dsimp [preCost] at *; omega) hb

/-- Two trailing explicit zeros encode 0(10)^q0 after the implicit
blank right tape, with no change in the physical initial tape. -/
private theorem word_zero_pad (q : Nat) :
    oppairs q ++ [false,false] =
      false :: (pairs q ++ [false]) := by
  induction q with
  | zero => rfl
  | succ q ih =>
      simpa [oppairs,pairs,List.append_assoc] using
        (congrArg (fun zs : List Bool => false :: true :: zs) ih)

/-- Canonical unpadded original-source E row (q may be zero):
not even a physically blank-left F/0 section occurs at a strictly
earlier positive time.  Unlike a literal l=[], this survives ObsEq. -/
theorem canonical_E_low_no_early_blank (k q : Nat) :
    ∀ t, 0<t → t<12*k*k+49*k+50+4*q →
      ¬ BlankLeftF
        (run t (init (List.replicate (3*k+2) true ++ oppairs q))) := by
  intro t hpos ht hblank
  let xs := List.replicate (3*k+2) true ++ oppairs q
  have hp := source_init_pad t 2 xs
  have hpblank : BlankLeftF
      (run t (init (xs ++ List.replicate 2 false))) :=
    (blankLeftF_congr hp).mp (by simpa [xs] using hblank)
  have hinput :
      init (xs ++ List.replicate 2 false) =
      init (List.replicate (3*k+2) true ++
        false :: (pairs q ++ [false])) := by
    simp only [xs,List.replicate_succ,List.replicate_zero,
      List.cons_append,List.append_assoc,List.append_nil]
    rw [word_zero_pad]
  rw [hinput] at hpblank
  exact (full_E_pairs_no_early_blank k q)
    t hpos ht hpblank

#print axioms blankLeftF_congr
#print axioms ePairs_toB_noBlank
#print axioms ePairs_no_early_blank
#print axioms full_E_pairs_no_early_blank
#print axioms canonical_E_low_no_early_blank

end BB6.CryptidELowCanonicalFirst
