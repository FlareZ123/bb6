import Raw56E1LESixClosed
import Raw56LE1LFPartialAll

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent1Raw56E1LE
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster

/-- The next exact E0 sibling is 1LF. Its source-generated child theorem leaves
    exactly one canonical residual, global E1=0LE index 17557. -/
def oneLF : PartialMachine := refine p (4,false) (some ⟨true,false,5⟩)
def remaining7 := remaining8.filter (fun e => !sameTable e.2 oneLF)
theorem count7 : remaining7.length = 7 := by decide

theorem eq1LFPartial :
    BB6.Agent1Raw56.LE1LFPartial.p = oneLF :=
  sameTable_sound (by decide)

theorem lf1_remaining_singleton :
    BB6.Agent1Raw56.LE1LFPartial.remaining1 =
      [BB6.Agent1Raw56.LE1LFPartial.remaining1.head!] := by
  cases h : BB6.Agent1Raw56.LE1LFPartial.remaining1 with
  | nil =>
    have hc := BB6.Agent1Raw56.LE1LFPartial.count1
    rw [h] at hc
    simp at hc
  | cons a xs =>
    cases xs with
    | nil => rfl
    | cons b ys =>
      have hc := BB6.Agent1Raw56.LE1LFPartial.count1
      rw [h] at hc
      simp at hc

abbrev hard17557 : PartialMachine :=
  BB6.Agent1Raw56.LE1LFPartial.remaining1.head!.2

/-- Refine the accepted eight-E0-child frontier by replacing the entire 1LF
    child with its sole exact canonical residual. -/
theorem sound7_plus_17557 :
    ∀ m, TNFQuotientCompatible p m →
      WeightedBound 40000 m ∨
      (∃ e ∈ remaining7, TNFQuotientCompatible e.2 m) ∨
      TNFQuotientCompatible hard17557 m := by
  intro m hm
  rcases sound8_closed m hm with hb | ⟨e, he, hq⟩
  · exact Or.inl hb
  · by_cases hmatch : sameTable e.2 oneLF = true
    · have heq : e.2 = oneLF := sameTable_sound hmatch
      have hq1 : TNFQuotientCompatible BB6.Agent1Raw56.LE1LFPartial.p m := by
        rw [eq1LFPartial]
        exact heq ▸ hq
      rcases BB6.Agent1Raw56.LE1LFPartial.sound1 m hq1 with
        hb1 | ⟨r, hr, hrq⟩
      · exact Or.inl (fun k d hk hd =>
          Nat.le_trans (hb1 k d hk hd) (by decide))
      · right
        right
        rw [lf1_remaining_singleton] at hr
        simp at hr
        subst r
        exact hrq
    · right
      left
      exact ⟨e, List.mem_filter.mpr ⟨he, by simp [hmatch]⟩, hq⟩

#print axioms count7
#print axioms lf1_remaining_singleton
#print axioms sound7_plus_17557
end BB6.Agent1Raw56E1LE
