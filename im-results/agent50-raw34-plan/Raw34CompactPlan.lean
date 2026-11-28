import Raw34WeightedPlan
import LastHole
import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Raw34Plan
open BB6Coverage BB6.Agent13BlankDelay

inductive CompactCert where
  | basic (c : Cert)
  | last (slot : Slot) (n : Nat)
  | far (d : Nat) (reflected : Bool) (c : BB6Coverage.FAR.Data d)

def compactCheck (B : Nat) (p : PartialMachine) : CompactCert → Bool
  | .basic c => weightedCheck B p c
  | .last s n => allOtherOrdinary p s && weightedCheck B (refine p s none) (.halt n)
  | .far _ reflected c =>
      c.fastValid (if reflected then BB6Coverage.FAR.reflectPartial p else p)

theorem compactCheck_sound (B : Nat) (p : PartialMachine) (cert : CompactCert)
    (h : compactCheck B p cert = true) : Cover (WeightedBound B) p := by
  cases cert with
  | basic c => exact weightedCheck_sound B p c h
  | last s n =>
    have hh : allOtherOrdinary p s = true ∧
        weightedCheck B (refine p s none) (.halt n) = true := by
      simpa only [compactCheck,Bool.and_eq_true] using h
    exact lastHole_cover p s hh.1 (weighted_of_never B)
      (weightedCheck_sound B (refine p s none) (.halt n) hh.2)
  | far d reflected c =>
    cases reflected with
    | false =>
      have hc : c.fastValid p = true := h
      exact .leaf p (fun m hm => weighted_of_never B m
        (c.sound p (c.fastValid_sound p hc) m hm))
    | true =>
      have hc : c.fastValid (BB6Coverage.FAR.reflectPartial p) = true := h
      exact .leaf p (fun m hm => weighted_of_never B m
        (BB6Coverage.FAR.reflectNever m
          (c.sound _ (c.fastValid_sound _ hc) _ (BB6Coverage.FAR.reflectCompatible p m hm))))

#print axioms compactCheck_sound
end BB6.Agent50Raw34Plan
