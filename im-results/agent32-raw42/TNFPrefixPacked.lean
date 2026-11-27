import TNFPackedBridge
import PrefixAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32PrefixPacked
open BB6Coverage BB6Coverage.Agent50Zipper BB6Coverage.Agent50SideCycle
open BB6.Agent50TNFPilot
open BB6Coverage.Agent10ZipAudit BB6Coverage.Agent13PackedZipper
open BB6.Agent50TNFPilot
open BB6.Agent3PackedCycle BB6.Agent3PrefixAudit BB6.Agent32Raw59QuickWeight
open BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent32PartialCut BB6.Agent8TNFPath
open BB6.Agent32PackedClosed

def quickHere (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) (z : H) : Bool :=
  decide (readP z.p = s) && (decide (p s = none) && quickWeight p s n B)

theorem quickHere_eq (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) (z : H)
    (h : runH p n startH = some z) : quickHere B p n s z = quickPackedQuery B p n s := by
  have hp := runH_p p n startH
  rw [h] at hp
  have hread : readRunP p n = some (readP z.p) := by
    unfold readRunP
    change (runP p n startH.p).map readP = _
    rw [← hp]
    rfl
  simp only [quickHere,quickPackedQuery,hread,Option.some.injEq]

def leafAt (B : Nat) (p : PartialMachine) (t : Nat) (z : H) : Audit → Bool
  | .last n s => match runFrom p t z n with
    | none => false
    | some c => quickHere B p n s c && restOK p s
  | .cycle e k r b => decide (0 < k) && cycleFrom p t z e k r b
  | a => quickLeaf B p a

theorem leafAt_eq (B : Nat) (p : PartialMachine) (t : Nat) (z : H) (a : Audit)
    (hp : runH p t startH = some z) : leafAt B p t z a = quickLeaf B p a := by
  cases a with
  | last n s =>
    rw [leafAt,quickLeaf,runFrom_eq p t z hp]
    cases hr : runH p n startH with
    | none =>
      have h := runH_p p n startH
      rw [hr] at h
      have hz : readRunP p n = none := by
        unfold readRunP
        change (runP p n startH.p).map readP = _
        rw [← h]; rfl
      simp [quickPackedQuery,hz]
    | some c => change (quickHere B p n s c && restOK p s) = _; rw [quickHere_eq B p n s c hr]
  | cycle e k r b => simp only [leafAt,quickLeaf,BB6.Agent3PackedAudit.packedCheck,cycleFrom_eq p t z hp]
  | far rev d C => rfl
  | proven q safe => rfl
  | split n s kids => rfl

def prefixCut (B cut : Nat) (p : PartialMachine) (t : Nat) (z : H) : Cut → Bool
  | .keep => false
  | .closed a => leafAt B p t z a
  | .split n s kids => match runFrom p t z n with
    | none => false
    | some c => quickHere B p n s c && allMoves (fun mv =>
        if mv.next.val ≤ cut then prefixCut B (advanceCut cut mv) (refine p s (some mv)) n c (kids mv) else true)
termination_by structural a => a

theorem prefix_packed (B cut : Nat) (p : PartialMachine) (t : Nat) (z : H) (a : Cut)
    (hp : runH p t startH = some z)
    (h : prefixCut B cut p t z a = true) : closedCheck B cut p a = true := by
  induction a generalizing p cut t z with
  | keep => exact h
  | closed a => simpa only [prefixCut,leafAt_eq B p t z a hp,closedCheck] using h
  | split n s kids ih =>
    rw [prefixCut,runFrom_eq p t z hp] at h
    cases hr : runH p n startH with
    | none => simp [hr] at h
    | some c =>
      simp only [hr,Bool.and_eq_true] at h
      have hq : quickPackedQuery B p n s = true := (quickHere_eq B p n s c hr).symm.trans h.1
      have hu : p s = none := by
        simp only [quickPackedQuery,Bool.and_eq_true,decide_eq_true_eq] at hq
        exact hq.2.1
      simp only [closedCheck,Bool.and_eq_true]
      refine ⟨hq,allMoves_of _ ?_⟩
      intro mv
      have hm := allMoves_sound _ h.2 mv
      split
      next hb => exact ih mv _ _ n c (runH_refine hu n startH c hr) (by simpa only [if_pos hb] using hm)
      next => rfl

def prefixRoot (B cut : Nat) (p : PartialMachine) (a : Cut) : Bool :=
  prefixCut B cut p 0 startH a

theorem prefix_zip (B cut : Nat) (p : PartialMachine) (a : Cut)
    (h : prefixRoot B cut p a = true) : BB6.Agent32Closed.closedCheck B cut p a = true :=
  BB6.Agent32PackedBridge.packed_closed B cut p a (prefix_packed B cut p 0 startH a rfl h)
#print axioms prefix_zip
end BB6.Agent32PrefixPacked
