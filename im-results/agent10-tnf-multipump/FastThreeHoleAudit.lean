import ThreeHoleAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10FastAudit
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole
open BB6Coverage.Agent50SideCycle

/-- A successful finite partial run has every earlier prefix. -/
theorem prefix_exists (p : PartialMachine) (n k : Nat) (c d : FinRayCfg)
    (h : finitePartialRun p n c = some d) (hk : k ≤ n) :
    ∃ e, finitePartialRun p k c = some e := by
  induction n generalizing k d with
  | zero =>
    have he : k = 0 := by omega
    subst k
    exact ⟨c,rfl⟩
  | succ n ih =>
    by_cases he : k = n+1
    · subst k
      exact ⟨d,h⟩
    · cases hr : finitePartialRun p n c with
      | none => simp [finitePartialRun,hr] at h
      | some e => exact ih k e hr (by omega)

/-- Single-pass window verification implies the original checker. -/
theorem fastSideCycleCheck_old (p : PartialMachine) (entry period : Nat)
    (right : Bool) (boundary : Int)
    (h : fastSideCycleCheck p entry period right boundary = true) :
    finiteSideCycleCheck p entry period right boundary = true := by
  cases hc : finitePartialRun p entry finiteBlank with
  | none => simp [fastSideCycleCheck,hc] at h
  | some c =>
    cases hd : finiteWindow p right boundary period c with
    | none => simp [fastSideCycleCheck,hc,hd] at h
    | some d =>
      have ht : finiteTailEq right boundary c d = true := by
        simpa [fastSideCycleCheck,hc,hd] using h
      obtain ⟨hr,hw⟩ := finiteWindow_sound p right boundary period c d hd
      simp only [finiteSideCycleCheck,hc,hr,Bool.and_eq_true]
      refine ⟨ht,List.all_eq_true.mpr ?_⟩
      intro j hj
      have hj' := List.mem_range.mp hj
      obtain ⟨e,he⟩ := prefix_exists p period j c d hr (by omega)
      rw [he]
      exact decide_eq_true (hw j hj' e he)

def fastCheck (B : Nat) (p : PartialMachine) : (t : Audit) → Bool
  | .last n s => queryOK B p n s && restOK p s
  | .cycle e k r b => decide (0 < k) && fastSideCycleCheck p e k r b
  | .far rev _ C => C.fastValid (if rev then FAR.reflectPartial p else p)
  | .proven q _ => tableOK p q
  | .split n s kids => queryOK B p n s &&
      allMoves (fun mv => fastCheck B (refine p s (some mv)) (kids mv))
termination_by structural t => t

theorem fastCheck_sound (B : Nat) (p : PartialMachine) (t : Audit)
    (h : fastCheck B p t = true) : check B p t = true := by
  induction t generalizing p with
  | last n s => exact h
  | cycle e k r b =>
    simp only [fastCheck, Bool.and_eq_true] at h
    simp only [check, Bool.and_eq_true]
    exact ⟨h.1,fastSideCycleCheck_old p e k r b h.2⟩
  | far rev d C => exact h
  | proven q safe => exact h
  | split n s kids ih =>
    simp only [fastCheck, Bool.and_eq_true] at h
    simp only [check, Bool.and_eq_true]
    exact ⟨h.1,allMoves_of _ (fun mv => ih mv _ (allMoves_sound _ h.2 mv))⟩

noncomputable def certifiedFast (B : Nat) (p : PartialMachine) (t : Audit)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p)
    (h : fastCheck B p t = true) : WeightedTNFCertificate B p 6 :=
  certified B p t hroot hno (fastCheck_sound B p t h)

#print axioms fastSideCycleCheck_old
#print axioms fastCheck_sound
#print axioms certifiedFast
end BB6.Agent10FastAudit
