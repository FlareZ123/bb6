import Raw47D3U61
import Raw47Late61Macro
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent50Raw47Late61Parent
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier BB6.Agent50FastKey
abbrev p := BB6.Agent50.Raw47D3U61.p
abbrev q := BB6.Agent50Raw47Late61Macro.p
abbrev remaining := BB6.Agent50.Raw47D3U61.remaining
abbrev expectedKeys := BB6.Agent50.Raw47D3U61.expectedKeys

theorem exact_key : tableCode q = 25578468639170103 := by decide +kernel

theorem only_remaining (e : List Move × PartialMachine) (he : e ∈ remaining) : e.2 = q := by
  have hm : tableCode e.2 ∈ BB6.Agent50.Raw47D3U61.remainingKeys := List.mem_map.mpr ⟨e, he, rfl⟩
  have hh := List.all_eq_true.mp BB6.Agent50.Raw47D3U61.remaining_key_set.1 _ hm
  have hkey : tableCode e.2 = 25578468639170103 := by
    simpa [BB6.Agent50.Raw47D3U61.expectedKeys] using hh
  exact tableCode_inj (hkey.trans exact_key.symm)

theorem all_quotient (m : Machine) (hm : TNFQuotientCompatible p m) : WeightedBound 143977 m := by
  rcases BB6.Agent50.Raw47D3U61.local_sound m hm with hb | ⟨e, he, hq⟩
  · exact fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide)
  · rw [only_remaining e he] at hq
    exact BB6.Agent50Raw47Late61Macro.all_quotient m hq

#print axioms only_remaining
#print axioms all_quotient
end BB6.Agent50Raw47Late61Parent
