import ThreeHoleAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent2Raw124FastAudit
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6Coverage.Agent50SideCycle

/-- The finite representation is exactly the partial semantics, including
    the case where an unknown or assigned halt terminates the run. -/
private theorem step_eq (p : PartialMachine) (c : FinRayCfg) :
    (finitePartialStep p c).map embedFinRay = knownStep p (embedFinRay c) := by
  cases h : p (c.state, finiteTape c c.head) with
  | none => simp [finitePartialStep,knownStep,readSlot,embedFinRay,h]
  | some t =>
    cases t with
    | none => simp [finitePartialStep,knownStep,readSlot,embedFinRay,h]
    | some mv =>
      unfold finitePartialStep knownStep
      change (((p (c.state,finiteTape c c.head)).bind id).map (finiteMove c)).map embedFinRay =
        ((p (c.state,finiteTape c c.head)).getD none).map (applyMove (embedFinRay c))
      rw [h]
      exact congrArg some (embedFinRay_move c mv)
private theorem run_eq (p : PartialMachine) (n : Nat) :
    (finitePartialRun p n finiteBlank).map embedFinRay = knownRun p n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases h : finitePartialRun p n finiteBlank with
    | none => simp [h] at ih; simp [finitePartialRun,knownRun,h,← ih]
    | some c =>
      rw [h] at ih
      rw [knownRun,← ih]
      simp only [Option.map_some,Option.bind_some,finitePartialRun,h]
      exact step_eq p c

def fastQuery (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) : Bool :=
  decide ((finitePartialRun p n finiteBlank).map (fun c => (c.state,finiteTape c c.head)) = some s) &&
    (decide (p s = none) && weightOK p s n B)

theorem query_eq (B : Nat) (p : PartialMachine) (n : Nat) (s : Slot) :
    fastQuery B p n s = queryOK B p n s := by
  unfold fastQuery queryOK
  rw [← run_eq p n]
  cases h : finitePartialRun p n finiteBlank <;> rfl

private theorem prefix_live (p : PartialMachine) (n j : Nat) (c d : FinRayCfg)
    (h : finitePartialRun p n c = some d) (hj : j ≤ n) : ∃ e, finitePartialRun p j c = some e := by
  induction n generalizing d with
  | zero =>
    have he : j=0 := by omega
    subst j
    exact ⟨d,h⟩
  | succ n ih =>
    by_cases he : j=n+1
    · subst j; exact ⟨d,h⟩
    · cases hr : finitePartialRun p n c with
      | none => simp [finitePartialRun,hr] at h
      | some e => exact ih e hr (by omega)

/-- A linear-pass certificate implies the legacy range-of-prefixes checker. -/
private theorem cycle_imp (p : PartialMachine) (e k : Nat) (r : Bool) (b : Int)
    (h : fastSideCycleCheck p e k r b = true) : finiteSideCycleCheck p e k r b = true := by
  cases hc : finitePartialRun p e finiteBlank with
  | none => simp [fastSideCycleCheck,hc] at h
  | some c =>
    cases hd : finiteWindow p r b k c with
    | none => simp [fastSideCycleCheck,hc,hd] at h
    | some d =>
      have ht : finiteTailEq r b c d = true := by simpa [fastSideCycleCheck,hc,hd] using h
      obtain ⟨hr,hw⟩ := finiteWindow_sound p r b k c d hd
      simp only [finiteSideCycleCheck,hc,hr,ht,Bool.true_and]
      apply List.all_eq_true.mpr
      intro j hj
      have hj' := List.mem_range.mp hj
      obtain ⟨f,hf⟩ := prefix_live p k j c d hr (by omega)
      have hs := hw j hj' f hf
      simp [hf,hs]

def fastCheck (B : Nat) (p : PartialMachine) : (t : Audit) → Bool
  | .last n s => fastQuery B p n s && restOK p s
  | .cycle e k r b => decide (0 < k) && fastSideCycleCheck p e k r b
  | .far rev _ C => C.fastValid (if rev then FAR.reflectPartial p else p)
  | .proven q _ => tableOK p q
  | .split n s kids => fastQuery B p n s &&
      allMoves (fun mv => fastCheck B (refine p s (some mv)) (kids mv))
termination_by structural t => t

theorem fastCheck_sound (B : Nat) (p : PartialMachine) (t : Audit)
    (h : fastCheck B p t = true) : check B p t = true := by
  induction t generalizing p with
  | last n s => simpa only [fastCheck,query_eq,check] using h
  | cycle e k r b =>
    have hh : decide (0<k) = true ∧ fastSideCycleCheck p e k r b = true := by
      simpa only [fastCheck,Bool.and_eq_true] using h
    simpa only [check,Bool.and_eq_true] using And.intro hh.1 (cycle_imp p e k r b hh.2)
  | far rev d C => exact h
  | proven q safe => exact h
  | split n s kids ih =>
    have hh : fastQuery B p n s = true ∧ allMoves (fun mv => fastCheck B (refine p s (some mv)) (kids mv)) = true := by
      simpa only [fastCheck,Bool.and_eq_true] using h
    simp only [check,Bool.and_eq_true]
    refine ⟨(query_eq B p n s) ▸ hh.1,allMoves_of _ ?_⟩
    intro mv
    exact ih mv _ (allMoves_sound _ hh.2 mv)

noncomputable def fastCertified (B : Nat) (p : PartialMachine) (t : Audit)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p) (h : fastCheck B p t = true) : WeightedTNFCertificate B p 6 :=
  certified B p t hroot hno (fastCheck_sound B p t h)
#print axioms fastCheck_sound
#print axioms fastCertified
end BB6.Agent2Raw124FastAudit
