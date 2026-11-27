import ZipPrefixAudit
set_option maxHeartbeats 0
namespace BB6.Agent6TNFGraph
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent50TNFPilot
open BB6Coverage.Agent50Zipper BB6Coverage.Agent10ZipAudit BB6.Agent48PrefixAudit

def graphOK (p : PartialMachine) (mask : Nat) : Bool :=
  (List.finRange 6).all fun q => if mask.testBit q.val then
    [false,true].all fun b => match p (q,b) with
      | some (some mv) => mask.testBit mv.next.val
      | _ => false
    else true

theorem graphStep (p : PartialMachine) (mask : Nat) (h : graphOK p mask = true)
    (c : Config) (hc : mask.testBit c.state.val = true) :
    ∃ d, knownStep p c = some d ∧ mask.testBit d.state.val = true := by
  have hq := List.all_eq_true.mp h c.state (List.mem_finRange c.state)
  simp only [hc,ite_true] at hq
  have hb : c.tape c.head ∈ [false,true] := by cases c.tape c.head <;> simp
  have hs := List.all_eq_true.mp hq _ hb
  cases hp : p (readSlot c) with
  | none => simp [hp] at hs
  | some t =>
    cases t with
    | none => simp [hp] at hs
    | some mv =>
      exact ⟨applyMove c mv, by simp [knownStep,hp], by simpa [hp,applyMove] using hs⟩

theorem runPrefix (p : PartialMachine) (n : Nat) (c : Config)
    (hc : knownRun p n = some c) : ∀ k ≤ n, ∃ d, knownRun p k = some d := by
  induction n generalizing c with
  | zero =>
    intro k hk
    have : k = 0 := by omega
    subst k
    exact ⟨c,hc⟩
  | succ n ih =>
    intro k hk
    by_cases he : k = n+1
    · subst k; exact ⟨c,hc⟩
    · cases hp : knownRun p n with
      | none => simp [knownRun,hp] at hc
      | some d => exact ih d hp k (by omega)

theorem graphForever (p : PartialMachine) (mask n : Nat) (c : Config)
    (hr : knownRun p n = some c) (hc : mask.testBit c.state.val = true)
    (hg : graphOK p mask = true) : weightedTNFKnownRunForever p := by
  have tail : ∀ k, ∃ d, knownRun p (n+k) = some d ∧ mask.testBit d.state.val = true := by
    intro k
    induction k with
    | zero => exact ⟨c,hr,hc⟩
    | succ k ih =>
      obtain ⟨d,hd,hq⟩ := ih
      obtain ⟨e,he,heq⟩ := graphStep p mask hg d hq
      exact ⟨e,by simp [knownRun,hd,he],heq⟩
  intro k
  by_cases hk : k ≤ n
  · exact runPrefix p n c hr k hk
  · obtain ⟨d,hd,_⟩ := tail (k-n)
    exact ⟨d,by rwa [show n+(k-n)=k by omega] at hd⟩

#print axioms graphForever
end BB6.Agent6TNFGraph
