import PackedCycle
import SparseFAR
import ZipThreeHoleAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent3SparseAudit
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6Coverage.Agent10ZipAudit
open BB6.Agent3PackedCycle BB6Coverage.Agent13PackedZipper

def packedQueryOK (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) : Bool :=
  decide (readRunP p n = some s) && (decide (p s = none) && weightOK p s n B)

theorem packedQueryOK_sound {B p n s} (h : packedQueryOK B p n s = true) :
    (knownRun p n).map readSlot = some s ∧ p s = none ∧ weightOK p s n B = true := by
  apply queryOK_sound
  simpa only [packedQueryOK,readRunP_eq,zipRead_eq,queryOK] using h

inductive SparseAudit where
  | last (n : Nat) (s : Slot)
  | cycle (entry period : Nat) (right : Bool) (boundary : Int)
  | far (rev : Bool) (d : Nat) (C : FAR.Data d) (S : FAR.Sparse.Rows)
  | proven (p : PartialMachine) (safe : ∀ m, compatible p m → NeverHalts m)
  | split (n : Nat) (s : Slot) (kids : Move → SparseAudit)

def byMoveS (xs : List SparseAudit) (mv : Move) : SparseAudit :=
  xs[12*mv.write.toNat+6*mv.right.toNat+mv.next.val]?.getD (.last 0 (0,false))

theorem sparseFarSound {d : Nat} (p : PartialMachine) (rev : Bool) (C : FAR.Data d)
    (S : FAR.Sparse.Rows)
    (h : FAR.Sparse.check C S (if rev then FAR.reflectPartial p else p) = true) :
    ∀ m, compatible p m → NeverHalts m := by
  intro m hm
  cases rev
  · exact FAR.Sparse.sound C S p h m hm
  · exact FAR.reflectNever m (FAR.Sparse.sound C S (FAR.reflectPartial p)
      h (reflectTable m) (FAR.reflectCompatible p m hm))

def sparseCheck (B : Nat) (p : PartialMachine) : (t : SparseAudit) → Bool
  | .last n s => packedQueryOK B p n s && restOK p s
  | .cycle e k r b => decide (0 < k) && cycleH p e k r b
  | .far rev _ C S => FAR.Sparse.check C S (if rev then FAR.reflectPartial p else p)
  | .proven q _ => tableOK p q
  | .split n s kids => packedQueryOK B p n s &&
      allMoves (fun mv => sparseCheck B (refine p s (some mv)) (kids mv))
termination_by structural t => t

noncomputable def certifiedSparse (B : Nat) (p : PartialMachine) (t : SparseAudit)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p)
    (h : sparseCheck B p t = true) : WeightedTNFCertificate B p 6 := by
  induction t generalizing p with
  | last n s =>
    have hv : packedQueryOK B p n s = true ∧ restOK p s = true := by
      simpa only [sparseCheck, Bool.and_eq_true] using h
    obtain ⟨hread,hhole,hw⟩ := packedQueryOK_sound hv.1
    cases hr : knownRun p n with
    | none => simp [hr] at hread
    | some c =>
      have hs : readSlot c = s := by simpa [hr] using hread
      exact .lastHole hroot (support6 p) (by decide) hr
        (by simpa [hs] using hhole)
        (by simpa [hs] using restOK_sound p s hv.2)
        (by simpa [hs] using weightOK_sound p s n B hw)
  | cycle e k r b =>
    have hv : 0 < k ∧ cycleH p e k r b = true := by
      simpa only [sparseCheck, Bool.and_eq_true, decide_eq_true_eq] using h
    exact .nonhalt hroot (support6 p) hno (cycleH_sound p e k r b hv.1 hv.2)
  | far rev d C S =>
    exact .nonhalt hroot (support6 p) hno (sparseFarSound p rev C S (by simpa only [sparseCheck] using h))
  | proven q safe =>
    have he : p = q := tableOK_sound p q (by simpa only [sparseCheck] using h)
    subst q
    exact .nonhalt hroot (support6 p) hno safe
  | split n s kids ih =>
    have hv : packedQueryOK B p n s = true ∧
        allMoves (fun mv => sparseCheck B (refine p s (some mv)) (kids mv)) = true := by
      simpa only [sparseCheck, Bool.and_eq_true] using h
    obtain ⟨hread,hhole,hw⟩ := packedQueryOK_sound hv.1
    cases hr : knownRun p n with
    | none => simp [hr] at hread
    | some c =>
      have hs : readSlot c = s := by simpa [hr] using hread
      refine .expand hroot (support6 p) (by decide) hno hr
        (by simpa [hs] using hhole)
        (by simpa [hs] using weightOK_sound p s n B hw) ?_ ?_
      · intro mv _
        have hchild := allMoves_sound _ hv.2 mv
        have hr' := refine_preserves_firstOne p s (some mv) hhole hroot
        have hn' := weightedTNFNoAssignedHalt_refine p s mv hno
        simpa only [hs] using ih mv (refine p s (some mv)) hr' hn' hchild
      · intro q hq _ _
        have hlt := q.isLt
        omega


#print axioms certifiedSparse
end BB6.Agent3SparseAudit
