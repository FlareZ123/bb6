import BB429NewResidue
import BB429LowOddMod8
import BB429Extra11
import Lean.Elab.Tactic.Omega

namespace BB429Q0Row237

open BB429NewResidue

theorem noReach_even_bad (a b : Nat) (ha : 0 < a) (he : a % 2 = 0)
    (hb : b % 4 ≠ 2) : ¬ Reach a b := by
  intro hr
  rcases hr with ⟨n, hn⟩
  have h := BB429LowOddMod8.rooted_even_parity n a b hn ha he
  omega

theorem noReach_notAllowed (a b : Nat)
    (hnot : ¬ BB429Mod8.Allowed a b) : ¬ Reach a b := by
  intro hr
  rcases hr with ⟨n, hn⟩
  exact hnot (BB429NewResidue.reach_allowed a b hn)

theorem noReach_11_1 (a b : Nat) (ha : a % 16 = 11) (hb : b % 4 = 1) :
    ¬ Reach a b := by
  intro hr
  rcases hr with ⟨n, hn⟩
  have h := BB429Extra11.blank_not_11_1 n a b hn ha
  omega

theorem noReach_odd_split (a b : Nat) (ha : 13 ≤ a) (ho : a % 2 = 1)
    (hF : ¬ Reach ((a - 3) / 2) (b + a))
    (hS : ¬ Reach ((4 * a + b - 26) / 4) ((b + 4) / 2)) :
    ¬ Reach a b := by
  intro hr
  rcases BB429NewResidue.odd_back a b ha ho hr with
    ⟨x, y, hxy, hax, hby⟩ | ⟨x, y, hxy, hx, hy, hmod⟩
  · have hx' : x = (a - 3) / 2 := by omega
    apply hF
    rw [← hx', ← hby]
    exact hxy
  · have hx' : x = (4 * a + b - 26) / 4 := by omega
    have hy' : y = (b + 4) / 2 := by omega
    apply hS
    rw [← hx', ← hy']
    exact hxy

theorem noReach_odd_only_F (a b : Nat) (ha : 13 ≤ a) (ho : a % 2 = 1)
    (hb : b % 4 ≠ 2)
    (hF : ¬ Reach ((a - 3) / 2) (b + a)) :
    ¬ Reach a b := by
  intro hr
  rcases BB429NewResidue.odd_back a b ha ho hr with
    ⟨x, y, hxy, hax, hby⟩ | ⟨x, y, hxy, hx, hy, hmod⟩
  · have hx' : x = (a - 3) / 2 := by omega
    apply hF
    rw [← hx', ← hby]
    exact hxy
  · omega

theorem noReach_even (a b : Nat) (ha : 6 ≤ a) (he : a % 2 = 0)
    (hE : ¬ Reach ((4 * a + b - 14) / 4) (b / 2)) :
    ¬ Reach a b := by
  intro hr
  rcases BB429NewResidue.even_back a b ha he hr with
    ⟨x, y, hxy, hx, hy, hmod⟩
  have hx' : x = (4 * a + b - 14) / 4 := by omega
  have hy' : y = b / 2 := by omega
  apply hE
  rw [← hx', ← hy']
  exact hxy

theorem noReach_6948859 : ¬ Reach 6948859 422309761 := by
  apply noReach_11_1
  · omega
  · omega

theorem noReach_13897721 : ¬ Reach 13897721 408412040 :=
  noReach_odd_only_F 13897721 408412040 (by omega) (by omega) (by omega)
    noReach_6948859

theorem noReach_27795445 : ¬ Reach 27795445 380616595 :=
  noReach_odd_only_F 27795445 380616595 (by omega) (by omega) (by omega)
    noReach_13897721

theorem noReach_136847312 : ¬ Reach 136847312 162512853 :=
  noReach_even_bad 136847312 162512853 (by omega) (by omega) (by omega)

theorem noReach_55590893 : ¬ Reach 55590893 325025702 :=
  noReach_odd_split 55590893 325025702 (by omega) (by omega)
    noReach_27795445 noReach_136847312

theorem noReach_111181789 : ¬ Reach 111181789 213843913 :=
  noReach_odd_only_F 111181789 213843913 (by omega) (by omega) (by omega)
    noReach_55590893

theorem noReach_4259836 : ¬ Reach 4259836 427687826 :=
  noReach_even 4259836 427687826 (by omega) (by omega) noReach_111181789

theorem noReach_8519675 : ¬ Reach 8519675 419168151 :=
  noReach_odd_only_F 8519675 419168151 (by omega) (by omega) (by omega)
    noReach_4259836

theorem noReach_117571546 : ¬ Reach 117571546 201064401 :=
  noReach_even_bad 117571546 201064401 (by omega) (by omega) (by omega)

theorem noReach_P : ¬ Reach 17039353 402128798 :=
  noReach_odd_split 17039353 402128798 (by omega) (by omega)
    noReach_8519675 noReach_117571546

theorem noReach_34078709 : ¬ Reach 34078709 368050089 :=
  noReach_odd_only_F 34078709 368050089 (by omega) (by omega) (by omega)
    noReach_P

theorem noReach_68157421 : ¬ Reach 68157421 299892668 :=
  noReach_odd_only_F 68157421 299892668 (by omega) (by omega) (by omega)
    noReach_34078709

theorem noReach_136314845 : ¬ Reach 136314845 163577823 :=
  noReach_odd_only_F 136314845 163577823 (by omega) (by omega) (by omega)
    noReach_68157421

theorem noReach_27262969 : ¬ Reach 27262969 381681583 := by
  apply noReach_notAllowed
  intro h
  unfold BB429Mod8.Allowed at h
  omega

theorem noReach_54525941 : ¬ Reach 54525941 327155642 :=
  noReach_odd_split 54525941 327155642 (by omega) (by omega)
    noReach_27262969 noReach_136314845

/-- The q=0 value pair of the branch-10 (n,d)=(23,7) affine seed is not blank-reachable. -/
theorem branch10_q0_23_7 : ¬ Reach 109051885 218103757 :=
  noReach_odd_only_F 109051885 218103757 (by omega) (by omega) (by omega)
    noReach_54525941

end BB429Q0Row237
