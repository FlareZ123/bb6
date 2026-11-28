import PackedFinite

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent48TreeLift
open BB6Coverage BB6.Agent49BoxBridge BB6.Agent48Box12 BB6.Agent48PackedFinite
open BB6.Agent49Box (Box Fits)
open BB6.Agent49Box6 (code fromCodes)

def residuals (B : Nat) (ext : PartialMachine → Bool) (domain : Box Slot Transition) (late : Slot) :
    Nat → Array Nat → Tree → List (Array Nat)
  | 0, cs, _ => [cs]
  | _+1, cs, .leaf w =>
      if pleaf B ext (fromCodes cs) w then []
      else (domain late).filterMap fun t =>
        let ds := setCode cs late t
        if pleaf B ext (fromCodes ds) w then none else some ds
  | fuel+1, cs, .split s kids =>
      (domain s).flatMap fun t =>
        let ds := setCode cs s t
        match kids[code t]? with
        | none => [ds]
        | some child => residuals B ext domain late fuel ds child

theorem residuals_sound (B : Nat) (ext : PartialMachine → Bool)
    (hExt : ∀ p, ext p = true → ∀ m, compatible p m → DecidedBelow B m)
    (domain : Box Slot Transition) (late : Slot) (fuel : Nat)
    (cs : Array Nat) (tree : Tree) (hs : cs.size = 12)
    (m : Machine) (hm : Fits domain m) (hp : compatible (fromCodes cs) m)
    (h : ∀ ds ∈ residuals B ext domain late fuel cs tree, compatible (fromCodes ds) m → DecidedBelow B m) :
    DecidedBelow B m := by
  induction fuel generalizing cs tree with
  | zero => exact h cs (by simp [residuals]) hp
  | succ fuel ih =>
    cases tree with
    | leaf w =>
      by_cases hc : pleaf B ext (fromCodes cs) w = true
      · exact pleaf_sound B ext hExt _ w hc m hp
      · let ds := setCode cs late (m late)
        have hd : compatible (fromCodes ds) m := by
          rw [fromCodes_set cs hs]
          exact compatible_refine _ _ _ hp
        by_cases he : pleaf B ext (fromCodes ds) w = true
        · exact pleaf_sound B ext hExt _ w he m hd
        · apply h ds _ hd
          simp only [residuals, hc]
          apply List.mem_filterMap.mpr
          exact ⟨m late, hm late, by simp [he, ds]⟩
    | split s kids =>
      let ds := setCode cs s (m s)
      have hd : compatible (fromCodes ds) m := by
        rw [fromCodes_set cs hs]
        exact compatible_refine _ _ _ hp
      cases hk : kids[code (m s)]? with
      | none =>
        apply h ds _ hd
        apply List.mem_flatMap.mpr
        exact ⟨m s, hm s, by simp [hk, ds]⟩
      | some child =>
        apply ih ds child (by simpa [ds,setCode] using hs) hd
        intro ps hps hpm
        apply h ps _ hpm
        apply List.mem_flatMap.mpr
        exact ⟨m s, hm s, by simpa [hk, ds] using hps⟩

#print axioms residuals_sound
end BB6.Agent48TreeLift
