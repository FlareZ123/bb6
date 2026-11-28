import TNFPackedClosed
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32PrefixClosed
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent32PartialCut BB6.Agent32Raw59QuickWeight BB6.Agent32PackedClosed
open BB6.Agent3PackedAudit BB6.Agent3PackedCycle BB6Coverage.Agent13PackedZipper BB6Coverage.Agent10ZipAudit

/-- Every successful known step reads an assigned slot, so refining an
    unassigned slot preserves that step. -/
theorem stepH_refine_unknown (p : PartialMachine) (s : Slot) (mv : Move)
    (hu : p s = none) (a b : H) (h : stepH p a = some b) :
    stepH (refine p s (some mv)) a = some b := by
  have hn : readP a.p ≠ s := by
    intro he
    simp [stepH,he,hu] at h
  simpa only [stepH,refine,if_neg hn] using h

theorem runH_refine_unknown (p : PartialMachine) (s : Slot) (mv : Move)
    (hu : p s = none) (n : Nat) (a b : H) (h : runH p n a = some b) :
    runH (refine p s (some mv)) n a = some b := by
  induction n generalizing a with
  | zero => exact h
  | succ n ih =>
    simp only [runH] at h ⊢
    cases hs : stepH p a with
    | none => simp [hs] at h
    | some c =>
      rw [stepH_refine_unknown p s mv hu a c hs]
      exact ih c (by simpa only [hs,Option.bind_some] using h)

theorem runH_add (p : PartialMachine) (n k : Nat) (a : H) :
    runH p (n+k) a = (runH p n a).bind (runH p k) := by
  induction n generalizing a with
  | zero => simp [runH]
  | succ n ih =>
    rw [show n+1+k = (n+k)+1 by omega]
    simp only [runH]
    cases hs : stepH p a with
    | none => rfl
    | some c => exact ih c

/-- Replay from a previously certified prefix, with a general fallback for
    certificates whose entry precedes that prefix. -/
def runAt (p : PartialMachine) (base : Nat) (z : H) (n : Nat) : Option H :=
  if base ≤ n then runH p (n-base) z else runH p n startH

theorem runAt_eq (p : PartialMachine) (base n : Nat) (z : H)
    (h : runH p base startH = some z) : runAt p base z n = runH p n startH := by
  unfold runAt
  split
  · rename_i hle
    have h' := runH_add p base (n-base) startH
    rw [show base+(n-base)=n by omega,h] at h'
    exact h'.symm
  · rfl

def queryAt (B : Nat) (p : PartialMachine) (base : Nat) (z : H) (n : Nat) (s : Slot) : Option H :=
  match runAt p base z n with
  | none => none
  | some c => if (decide (readP c.p = s) && decide (p s = none) && quickWeight p s n B) then some c else none

theorem runH_project (p : PartialMachine) (n : Nat) (z : H) :
    (runH p n z).map H.p = runP p n z.p := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [runH,runP,stepH,stepP]
    cases h : (p (readP z.p)).bind id with
    | none => rfl
    | some mv => exact ih (moveH mv z)

theorem queryAt_sound {B p base z n s c}
    (hprefix : runH p base startH = some z)
    (h : queryAt B p base z n s = some c) :
    runH p n startH = some c ∧ p s = none ∧ quickPackedQuery B p n s = true := by
  unfold queryAt at h
  rw [runAt_eq p base n z hprefix] at h
  cases hr : runH p n startH with
  | none => simp [hr] at h
  | some d =>
    simp only [hr] at h
    split at h
    · rename_i hd
      have he : d = c := Option.some.inj h
      subst d
      simp only [Bool.and_eq_true,decide_eq_true_eq] at hd
      refine ⟨rfl,hd.1.2,?_⟩
      have hp := runH_project p n startH
      rw [hr] at hp
      have hread : readRunP p n = some s := by
        unfold readRunP
        rw [show runP p n startP = some c.p from hp.symm]
        simp [hd.1.1]
      simp [quickPackedQuery,hread,hd.1.2,hd.2]
    · simp at h

/-- Uses the original packed side-cycle test, replaying only the suffix. -/
def cycleAt (p : PartialMachine) (base : Nat) (z : H)
    (e k : Nat) (r : Bool) (b : Int) : Bool :=
  match runAt p base z e with
  | none => false
  | some c => match windowH p r b k c with
    | none => false
    | some d => tailH r b c d

theorem cycleAt_eq (p : PartialMachine) (base : Nat) (z : H)
    (e k : Nat) (r : Bool) (b : Int) (h : runH p base startH = some z) :
    cycleAt p base z e k r b = cycleH p e k r b := by
  unfold cycleAt cycleH
  rw [runAt_eq p base e z h]
  rfl

def checkFrom (B cut : Nat) (p : PartialMachine) (base : Nat) (z : H) : Cut → Bool
  | .keep => false
  | .closed (.last n s) => (queryAt B p base z n s).isSome && restOK p s
  | .closed (.cycle e k r b) => decide (0 < k) && cycleAt p base z e k r b
  | .closed a => quickLeaf B p a
  | .split n s kids => match queryAt B p base z n s with
    | none => false
    | some c => allMoves (fun mv => if mv.next.val ≤ cut then
        checkFrom B (advanceCut cut mv) (refine p s (some mv)) n c (kids mv) else true)
termination_by structural t => t

theorem checkFrom_sound (B cut : Nat) (p : PartialMachine) (base : Nat) (z : H) (t : Cut)
    (hprefix : runH p base startH = some z) (h : checkFrom B cut p base z t = true) :
    closedCheck B cut p t = true := by
  induction t generalizing p cut base z with
  | keep => simp [checkFrom] at h
  | closed a =>
    cases a with
    | last n s =>
      simp only [checkFrom,Bool.and_eq_true] at h
      cases hq : queryAt B p base z n s with
      | none => simp [hq] at h
      | some c =>
        have hs := queryAt_sound hprefix hq
        simp [closedCheck,quickLeaf,hs.2.2,h.2]
    | cycle e k r b =>
      simpa only [checkFrom,cycleAt_eq p base z e k r b hprefix,closedCheck,quickLeaf,packedCheck] using h
    | far rev d C => exact h
    | proven q safe => exact h
    | split n s kids => exact h
  | split n s kids ih =>
    simp only [checkFrom] at h
    cases hq : queryAt B p base z n s with
    | none => simp [hq] at h
    | some c =>
      have hs := queryAt_sound hprefix hq
      apply split_checked B cut p n s kids hs.2.2
      intro mv
      split
      · rename_i hm
        have hc := allMoves_sound _ (by simpa only [hq] using h) mv
        apply ih mv (advanceCut cut mv) (refine p s (some mv)) n c
        · exact runH_refine_unknown p s mv hs.2.1 n startH c hs.1
        · simpa only [if_pos hm] using hc
      · rfl

def fastClosedCheck (B cut : Nat) (p : PartialMachine) (t : Cut) : Bool :=
  checkFrom B cut p 0 startH t

theorem fastClosedCheck_sound {B cut p t} (h : fastClosedCheck B cut p t = true) :
    closedCheck B cut p t = true := checkFrom_sound B cut p 0 startH t rfl h

#print axioms fastClosedCheck_sound
end BB6.Agent32PrefixClosed
