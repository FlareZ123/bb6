import OneLALate3318
namespace BB6.Agent48OneLALate.R3318
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent3PackedAudit BB6Coverage.Agent13PackedZipper

theorem checked_sharp : packedCheck 881052 parent (.last 881051 (5,false)) = true := by
  simp only [packedCheck,packedQueryOK,readRunP,reached,Option.map_some]
  decide +kernel

theorem all_completions_sharp : ∀ m, compatible parent m → WeightedBound 881052 m :=
  (certifiedPacked 881052 parent _ root nohalt checked_sharp).sound

def halter : Machine := weightedTNFDefaultCompletion parent

theorem halter_compatible : compatible parent halter := weightedTNFDefaultCompletion_compatible _

theorem halter_time : HaltsAfter halter 881051 := by
  have hc : packedQueryOK 881052 parent 881051 (5,false) = true := by
    have h : packedQueryOK 881052 parent 881051 (5,false) = true ∧ BB6.Agent50TNFPilot.restOK parent (5,false) = true := by
      simpa only [packedCheck, Bool.and_eq_true] using checked_sharp
    exact h.1
  obtain ⟨hread,hhole,hw⟩ := packedQueryOK_sound hc
  apply (weightedTNF_halt_iff_firstHole parent nohalt 881051).mpr
  cases hr : knownRun parent 881051 with
  | none => simp [hr] at hread
  | some c =>
    have hs : readSlot c = (5,false) := by simpa [hr] using hread
    exact ⟨c, rfl, by simpa [hs] using hhole⟩

theorem sharp_lower (B : Nat) (h : WeightedBound B halter) : 881052 ≤ B := by
  have hd : 0 ∈ delays (zeroNext halter) 0 := by decide +kernel
  exact h 881051 0 halter_time hd
#print axioms all_completions_sharp
#print axioms halter_time
#print axioms sharp_lower
end BB6.Agent48OneLALate.R3318
