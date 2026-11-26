import Raw55Cut
import Raw55Sweep
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw55Progress
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot
open BB6.Agent25Raw55Cut (canonicalRemaining)
open BB6.Agent25Raw55Sweep (Kind)

def equalTable (p q : PartialMachine) : Bool :=
  (List.finRange 6).all fun i => [false,true].all fun b => decide (p (i,b) = q (i,b))

theorem equalTable_sound {p q : PartialMachine} (h : equalTable p q = true) : p = q := by
  funext s
  rcases s with ⟨i,b⟩
  have hi := List.all_eq_true.mp h i (List.mem_finRange i)
  have hb : b ∈ [false,true] := by cases b <;> simp
  exact of_decide_eq_true (List.all_eq_true.mp hi b hb)

def kinds : List Kind := [.viaA,.viaB,.direct]
def sweepMatch (p : PartialMachine) : Bool :=
  kinds.any (fun k => equalTable p (BB6.Agent25Raw55Sweep.table k))
def remaining := canonicalRemaining.filter (fun e => !sweepMatch e.2)

theorem remaining_count : remaining.length = 271 := by decide

theorem sweepWeighted (k : Kind) (m : Machine)
    (hm : compatible (BB6.Agent25Raw55Sweep.table k) m) : WeightedBound 7014 m := by
  intro n d hn hd
  have h := BB6.Agent25Raw55Sweep.never k m hm (n+1)
  rw [hn.2] at h
  contradiction

theorem sweepRoot (k : Kind) :
    BB6.Agent25Raw55Sweep.table k initialSlot = some (some ⟨true,true,1⟩) := by
  cases k <;> decide

theorem refined (m : Machine) (hm : TNFQuotientCompatible BB6.Agent25Raw55Cut.parent m) :
    WeightedBound 7014 m ∨ ∃ e ∈ remaining, TNFQuotientCompatible e.2 m := by
  rcases BB6.Agent25Raw55Cut.canonical_local_sound m hm with h | ⟨e,he,hq⟩
  · exact Or.inl h
  · cases hh : sweepMatch e.2 with
    | false => exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [hh]⟩,hq⟩
    | true =>
      obtain ⟨k,hk,hmatch⟩ := List.any_eq_true.mp hh
      have heq := equalTable_sound hmatch
      rw [heq] at hq
      exact Or.inl (quotientSafe (sweepRoot k) (sweepWeighted k) m hq)

#print axioms remaining_count
#print axioms sweepWeighted
#print axioms refined
end BB6.Agent25Raw55Progress
