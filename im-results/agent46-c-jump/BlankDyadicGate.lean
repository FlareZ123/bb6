import SectionCompleteBasin
import Agent46CBridge

namespace BB6.Agent46

private theorem halts_iff_predecessor {α : Type} (f : α → Option α) (x : α) :
    (∃ n, BB6.Agent8Section.run f n (some x) = none) ↔
    (∃ m s, BB6.Agent8Section.run f m (some x)=some s ∧ f s=none) := by
  constructor
  · rintro ⟨n,hn⟩
    have aux : ∀ n, BB6.Agent8Section.run f n (some x)=none →
        ∃ m s, BB6.Agent8Section.run f m (some x)=some s ∧ f s=none := by
      intro n
      induction n with
      | zero =>
        intro h
        simp [BB6.Agent8Section.run] at h
      | succ n ih =>
        intro h
        cases hs : BB6.Agent8Section.run f n (some x) with
        | none => exact ih hs
        | some s =>
          refine ⟨n,s,hs,?_⟩
          change (BB6.Agent8Section.run f n (some x)).bind f=none at h
          simpa only [hs,Option.bind_some] using h
    exact aux n hn
  · rintro ⟨m,s,hm,hf⟩
    refine ⟨m+1,?_⟩
    change (BB6.Agent8Section.run f m (some x)).bind f=none
    simp [hm,hf]

theorem blank_halts_iff_reaches_dyadic_target :
    BB6.CReachBridge.RunHalts ↔
      ∃ m a k, BB6.Agent8Section.run secNext m (some (5,1))=some (a,k) ∧
        SectionHaltTarget a k := by
  rw [blank_halts_iff_arithmetic]
  rw [halts_iff_predecessor secNext (5,1)]
  constructor
  · rintro ⟨m, ⟨a,k⟩,hm,ht⟩
    exact ⟨m,a,k,hm,(section_none_iff_target a k).mp ht⟩
  · rintro ⟨m,a,k,hm,ht⟩
    exact ⟨m,(a,k),hm,(section_none_iff_target a k).mpr ht⟩

#print axioms blank_halts_iff_reaches_dyadic_target
end BB6.Agent46
