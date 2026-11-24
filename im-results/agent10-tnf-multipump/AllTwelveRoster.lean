import Raw86Data
import Raw87Data
import Raw88Data
import Raw91Data
import Raw92Data
import Raw93Data
import Raw97Data
import Raw98Data
import Raw100Data
import Raw101Data
import Raw102Data
import Raw104Data
import FourHoleResidualRoster
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent10TwelveRoster
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31FourHoleRoster

def covered (p : PartialMachine) : Bool :=
  sameTable p BB6.Agent10Raw86.p86 ||
  sameTable p BB6.Agent10Raw87.p87 ||
  sameTable p BB6.Agent10Raw88.p88 ||
  sameTable p BB6.Agent10Raw91.p91 ||
  sameTable p BB6.Agent10Raw92.p92 ||
  sameTable p BB6.Agent10Raw93.p93 ||
  sameTable p BB6.Agent10Raw97.p97 ||
  sameTable p BB6.Agent10Raw98.p98 ||
  sameTable p BB6.Agent10Raw100.p100 ||
  sameTable p BB6.Agent10Raw101.p101 ||
  sameTable p BB6.Agent10Raw102.p102 ||
  sameTable p BB6.Agent10Raw104.p104

theorem covered_sound (p : PartialMachine) (h : covered p = true)
    (m : Machine) (hm : compatible p m) : WeightedBound 7014 m := by
  simp only [covered, Bool.or_eq_true] at h
  rcases h with (((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h)
  · have he := sameTable_sound h
    have hb := BB6.Agent10Raw86.all86 m (he ▸ hm)
    intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) (by decide)
  · have he := sameTable_sound h
    have hb := BB6.Agent10Raw87.all87 m (he ▸ hm)
    intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) (by decide)
  · have he := sameTable_sound h
    have hb := BB6.Agent10Raw88.all88 m (he ▸ hm)
    intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) (by decide)
  · have he := sameTable_sound h
    have hb := BB6.Agent10Raw91.all91 m (he ▸ hm)
    intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) (by decide)
  · have he := sameTable_sound h
    have hb := BB6.Agent10Raw92.all92 m (he ▸ hm)
    intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) (by decide)
  · have he := sameTable_sound h
    have hb := BB6.Agent10Raw93.all93 m (he ▸ hm)
    intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) (by decide)
  · have he := sameTable_sound h
    have hb := BB6.Agent10Raw97.all97 m (he ▸ hm)
    intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) (by decide)
  · have he := sameTable_sound h
    have hb := BB6.Agent10Raw98.all98 m (he ▸ hm)
    intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) (by decide)
  · have he := sameTable_sound h
    have hb := BB6.Agent10Raw100.all100 m (he ▸ hm)
    intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) (by decide)
  · have he := sameTable_sound h
    have hb := BB6.Agent10Raw101.all101 m (he ▸ hm)
    intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) (by decide)
  · have he := sameTable_sound h
    have hb := BB6.Agent10Raw102.all102 m (he ▸ hm)
    intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) (by decide)
  · have he := sameTable_sound h
    have hb := BB6.Agent10Raw104.all104 m (he ▸ hm)
    intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) (by decide)

noncomputable def reducedRoster := remainingRootRoster.filter fun e => !(covered e.2)

theorem reduced_count : reducedRoster.length = 112 := by decide

theorem reduced_sound (m : Machine) (hm : compatible firstOneCylinder m) :
    WeightedBound 7014 m ∨ ∃ e ∈ reducedRoster, compatible e.2 m := by
  rcases remainingRootRoster_sound_7014 m hm with h | ⟨e,he,hp⟩
  · exact Or.inl h
  · cases hc : covered e.2 with
    | true => exact Or.inl (covered_sound e.2 hc m hp)
    | false => exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [hc]⟩,hp⟩

#print axioms covered_sound
#print axioms reduced_count
#print axioms reduced_sound
end BB6.Agent10TwelveRoster
