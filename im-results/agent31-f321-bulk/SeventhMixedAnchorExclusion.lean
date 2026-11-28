import FirstMixedAnchorExclusion
import HighFarRootTargets
import Lean.Elab.Tactic.Omega

/-!
Exact root exclusion for the seventh member of the dangerous
H^(24k+22)/Far terminal-suffix family (k=6).
-/

set_option maxRecDepth 1000000

namespace BB6.Agent31F321SeventhMixed
open BB6.Agent31F321Density
open BB6.Agent31F321FirstMixed
open BB6.Agent31F321HighFarRootTargets

theorem root_at_25294 :
    CounterReach 1 1 25294
      81093715175809501370326247837542228852702578472414
      93536104789177786765035829293842113257979682750461 :=
  rootIter_sound (by decide)

theorem root_at_25295 :
    CounterReach 1 1 25295
      324374860703238005481304991350168915410810313889662 1 :=
  rootIter_sound (by decide)

theorem root_at_25461 :
    CounterReach 1 1 25461
      549210604499529727804933331049938755579403793555618 2 :=
  rootIter_sound (by decide)

def seventhWindowFirsts : List (Option Nat) :=
  (List.range 166).map fun j =>
    (rootIter j 324374860703238005481304991350168915410810313889662 1).map Prod.fst

theorem seventh_target_not_in_window :
    some 106898405473346042017183804907248129437691066000486 ∉
      seventhWindowFirsts := by
  decide

theorem root_sum_before_25295
    {n A D : Nat}
    (hn : n≤25294)
    (hr : CounterReach 1 1 n A D) :
    A+D ≤ 174629819964987288135362077131384342110682261222875 := by
  obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le hn
  have h25294 :
      CounterReach 1 1 (n+m)
        81093715175809501370326247837542228852702578472414
        93536104789177786765035829293842113257979682750461 := by
    simpa [←hm] using root_at_25294
  rcases counterReach_split h25294 with ⟨a,d,hpre,htail⟩
  rcases counterReach_deterministic hr hpre with ⟨rfl,rfl⟩
  have hs := counterReach_sum_mono htail
  omega

theorem root_sum_after_25460
    {n A D : Nat}
    (hn : 25461≤n)
    (hr : CounterReach 1 1 n A D) :
    549210604499529727804933331049938755579403793555620 ≤ A+D := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hn
  rcases counterReach_split hr with ⟨a,d,hpre,htail⟩
  rcases counterReach_deterministic root_at_25461 hpre with ⟨rfl,rfl⟩
  have hs := counterReach_sum_mono htail
  omega

theorem seventh_window_first_not_target
    {n A D : Nat}
    (hlo : 25295≤n)
    (hhi : n≤25460)
    (hr : CounterReach 1 1 n A D) :
    A ≠ 106898405473346042017183804907248129437691066000486 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hlo
  have hj : j<166 := by omega
  rcases counterReach_split hr with ⟨a,d,hpre,htail⟩
  rcases counterReach_deterministic root_at_25295 hpre with ⟨rfl,rfl⟩
  have hcomp := rootIter_complete htail
  intro hA
  subst A
  have hmem :
      some 106898405473346042017183804907248129437691066000486 ∈
        seventhWindowFirsts := by
    unfold seventhWindowFirsts
    apply List.mem_map.mpr
    refine ⟨j,List.mem_range.mpr hj,?_⟩
    rw [hcomp]
    rfl
  exact seventh_target_not_in_window hmem

theorem seventh_mixed_anchor_middleOdd_predecessor_unreachable
    {n a d : Nat}
    (hr : CounterReach 1 1 n a d)
    (hR : 4*a+6=
      427593621893384168068735219628992517750764264001950)
    (h1 : a<d)
    (h2 : d<3*a+1) :
    False := by
  have ha :
      a=106898405473346042017183804907248129437691066000486 := by omega
  subst a
  by_cases hEarly : n≤25294
  · have hs := root_sum_before_25295 hEarly hr
    omega
  by_cases hLate : 25461≤n
  · have hs := root_sum_after_25460 hLate hr
    omega
  exact (seventh_window_first_not_target (by omega) (by omega) hr) rfl

theorem dangerR_six :
    dangerR 6 =
      427593621893384168068735219628992517750764264001950 := by
  decide

theorem seventh_danger_anchor_not_root
    {n a d : Nat}
    (hr : CounterReach 1 1 n a d)
    (ha : SmallAnchorMove a d (dangerR 6) 1) :
    False := by
  have hm := danger_anchor_requires_middleOdd hr ha
  rw [dangerR_six] at hm
  exact seventh_mixed_anchor_middleOdd_predecessor_unreachable
    hr hm.2.2.2 hm.1 hm.2.1

#print axioms root_at_25294
#print axioms root_at_25295
#print axioms root_at_25461
#print axioms seventh_target_not_in_window
#print axioms seventh_mixed_anchor_middleOdd_predecessor_unreachable
#print axioms seventh_danger_anchor_not_root
end BB6.Agent31F321SeventhMixed
