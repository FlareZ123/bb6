import TNFPilot
import SideCycle
import FastFAR

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31ThreeHole
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6Coverage.Agent50SideCycle

inductive Audit where
  | last (n : Nat) (s : Slot)
  | cycle (entry period : Nat) (right : Bool) (boundary : Int)
  | far (rev : Bool) (d : Nat) (C : FAR.Data d)
  | split (n : Nat) (s : Slot) (kids : Move → Audit)

def allMoves (f : Move → Bool) : Bool :=
  (List.finRange 6).all fun q => [false,true].all fun w =>
    [false,true].all fun r => f ⟨w,r,q⟩

theorem allMoves_sound (f : Move → Bool) (h : allMoves f = true)
    (mv : Move) : f mv = true := by
  rcases mv with ⟨w,r,q⟩
  have hq := List.all_eq_true.mp h q (List.mem_finRange q)
  have hw : w ∈ [false,true] := by cases w <;> simp
  have hr : r ∈ [false,true] := by cases r <;> simp
  exact List.all_eq_true.mp (List.all_eq_true.mp hq w hw) r hr

def queryOK (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) : Bool :=
  decide ((knownRun p n).map readSlot = some s) &&
    (decide (p s = none) && weightOK p s n B)

theorem queryOK_sound {B p n s} (h : queryOK B p n s = true) :
    (knownRun p n).map readSlot = some s ∧ p s = none ∧ weightOK p s n B = true := by
  simpa only [queryOK, Bool.and_eq_true, decide_eq_true_eq] using h

def check (B : Nat) (p : PartialMachine) : (t : Audit) → Bool
  | .last n s => queryOK B p n s && restOK p s
  | .cycle e k r b => decide (0 < k) && finiteSideCycleCheck p e k r b
  | .far rev _ C => C.fastValid (if rev then FAR.reflectPartial p else p)
  | .split n s kids => queryOK B p n s &&
      allMoves (fun mv => check B (refine p s (some mv)) (kids mv))
termination_by structural t => t

theorem farSound {d : Nat} (p : PartialMachine) (rev : Bool) (C : FAR.Data d)
    (h : C.fastValid (if rev then FAR.reflectPartial p else p) = true) :
    ∀ m, compatible p m → NeverHalts m := by
  intro m hm
  cases rev
  · exact C.sound p (C.fastValid_sound p h) m hm
  · exact FAR.reflectNever m (C.sound (FAR.reflectPartial p)
      (C.fastValid_sound _ h) (reflectTable m) (FAR.reflectCompatible p m hm))

def certified (B : Nat) (p : PartialMachine) (t : Audit)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p)
    (h : check B p t = true) : WeightedTNFCertificate B p 6 := by
  induction t generalizing p with
  | last n s =>
    have hv : queryOK B p n s = true ∧ restOK p s = true := by
      simpa only [check, Bool.and_eq_true] using h
    obtain ⟨hread,hhole,hw⟩ := queryOK_sound hv.1
    cases hr : knownRun p n with
    | none => simp [hr] at hread
    | some c =>
      have hs : readSlot c = s := by simpa [hr] using hread
      exact .lastHole hroot (support6 p) (by decide) hr
        (by simpa [hs] using hhole)
        (by simpa [hs] using restOK_sound p s hv.2)
        (by simpa [hs] using weightOK_sound p s n B hw)
  | cycle e k r b =>
    have hv : 0 < k ∧ finiteSideCycleCheck p e k r b = true := by
      simpa only [check, Bool.and_eq_true, decide_eq_true_eq] using h
    exact .nonhalt hroot (support6 p) hno (finiteSideCycleCheck_sound p e k r b hv.1 hv.2)
  | far rev d C =>
    exact .nonhalt hroot (support6 p) hno (farSound p rev C (by simpa only [check] using h))
  | split n s kids ih =>
    have hv : queryOK B p n s = true ∧
        allMoves (fun mv => check B (refine p s (some mv)) (kids mv)) = true := by
      simpa only [check, Bool.and_eq_true] using h
    obtain ⟨hread,hhole,hw⟩ := queryOK_sound hv.1
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

def byMove (xs : List Audit) (mv : Move) : Audit :=
  xs[12*mv.write.toNat+6*mv.right.toNat+mv.next.val]?.getD (.last 0 (0,false))

abbrev parent : PartialMachine := (pathEnd root 2 (path.take 8)).1

theorem parent_reachable : FirstHolePath parent 6 := by
  have hc : pathOK root 2 (path.take 8) = true := by decide
  exact pathOK_sound root 2 (path.take 8) FirstHolePath.root hc

theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  pathEnd_nohalt root 2 (path.take 8) firstOneCylinder_no_assigned_halt

end BB6.Agent31ThreeHole
