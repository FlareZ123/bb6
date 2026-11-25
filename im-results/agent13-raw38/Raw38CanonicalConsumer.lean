import Raw38ResidualClosure
import CanonicalPartialAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent13Raw38
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole
open BB6.Agent10ZipAudit BB6.Agent47PartialAudit BB6.Agent13CanonicalPartialAudit

theorem p38_support : TNFSupport p38 4 := by
  intro s t h
  rcases s with ⟨q,b⟩
  have hv : ∀ q : Fin 6, ∀ b : Bool, ∀ t : Transition,
      p38 (q,b) = some t → q.val < 4 ∧
      ∀ mv, t = some mv → mv.next.val < 4 := by decide
  exact hv q b t h

def canonicalRemaining38 :=
  (canonicalResiduals 4 p38 (cut38 kids38)).filter (fun e => !matches e.2)

theorem canonicalRemaining38_count : canonicalRemaining38.length = 12 := by decide
theorem canonicalRemaining38_depth :
    canonicalRemaining38.all (fun e => e.1.length == 1) = true := by decide

theorem canonical38_sound : ∀ m, TNFQuotientCompatible p38 m →
    WeightedBound 1000 m ∨
    ∃ e ∈ canonicalRemaining38, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases canonicalPartialSound 1000 4 p38 (cut38 kids38)
      (by decide) p38_support p38_root p38_nohalt (cut38_checked kids38 kids38_checked)
      m hm with hb | ⟨e, he, hc⟩
  · exact Or.inl hb
  · by_cases h : matches e.2 = true
    · obtain ⟨perm, hp, hcp⟩ := hc
      obtain ⟨perm0, hp0, hc0⟩ := hm
      have hz := firstOne_terminal p38 p38_root (renameTable perm0 m) hc0
      exact Or.inl (weighted_rename_back 1000 perm m hp
        ((zeroNext_none_rename_iff perm0 m hp0).mp hz)
        (weighted_never 1000 (renameTable perm m) (match_never e.2 h _ hcp)))
    · exact Or.inr ⟨e, List.mem_filter.mpr ⟨he, by simp [h]⟩, hc⟩

#print axioms canonical38_sound
#print axioms canonicalRemaining38_count
#print axioms canonicalRemaining38_depth
end BB6.Agent13Raw38
