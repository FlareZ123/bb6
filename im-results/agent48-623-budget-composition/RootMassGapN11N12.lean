import RootMassGapAllN10
import Lean.Elab.Tactic.Omega

/-!
# n=11 and n=12 root mass-corridor extensions

This file extends the finite blank-root mass exclusions using exact
source-shaped checkpoints 47--55. The new checkpoints are source propositions
proved by `decide` against Agent49ParitySource.run. This is intermediate
finite-scale evidence, not an all-time root invariant or a BB(6) decision.
-/

namespace BB6.Agent48RootMassGapN11N12

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent48TerminalBudgetCounterexample
open BB6.Agent8RootMassGapAllN10
open BB6.Agent8RootCancellationBudgetBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Exact blank-root checkpoint at step 47. -/
theorem root_run_47 :
    run 47 = some (.D 145494 1278161) := by decide

/-- Exact blank-root checkpoint at step 48. -/
theorem root_run_48 :
    run 48 = some (.D 1132670 436504) := by decide

/-- Exact blank-root checkpoint at step 49. -/
theorem root_run_49 :
    run 49 = some (.D 696164 1309542) := by decide

/-- Exact blank-root checkpoint at step 50. -/
theorem root_run_50 :
    run 50 = some (.D 613374 2088523) := by decide

/-- Exact blank-root checkpoint at step 51. -/
theorem root_run_51 :
    run 51 = some (.D 1475146 1840152) := by decide

/-- Exact blank-root checkpoint at step 52. -/
theorem root_run_52 :
    run 52 = some (.D 365000 4425473) := by decide

/-- Exact blank-root checkpoint at step 53. -/
theorem root_run_53 :
    run 53 = some (.D 4060470 1095032) := by decide

/-- Exact blank-root checkpoint at step 54. -/
theorem root_run_54 :
    run 54 = some (.D 2965430 3285134) := by decide

/-- Exact blank-root checkpoint at step 55. -/
theorem root_run_55 :
    run 55 = some (.D 319702 8896323) := by decide

/-- Near-strip mass bounds at scale 11. -/
theorem n11_near_mass_bounds (m M : Nat)
    (hmLo : 59046 <= m) (hmHi : m <= 177143)
    (hgap : absDiff (4*M) (7*m) <= 505) :
    162251 <= m+M ∧ m+M <= 487269 := by
  have h := absDiff_le_both (4*M) (7*m) 505 hgap
  omega

/-- Orientation-free form of the n=11 near-strip mass bounds. -/
theorem n11_near_mass_bounds_minmax (a d : Nat)
    (hmLo : 59046 <= min a d) (hmHi : min a d <= 177143)
    (hgap : absDiff (4*max a d) (7*min a d) <= 505) :
    162251 <= a+d ∧ a+d <= 487269 := by
  rcases le_total a d with had | hda
  · have hlo : 59046 <= a := by simpa [min_eq_left had] using hmLo
    have hhi : a <= 177143 := by simpa [min_eq_left had] using hmHi
    have hg : absDiff (4*d) (7*a) <= 505 := by
      simpa [min_eq_left had, max_eq_right had] using hgap
    have h := n11_near_mass_bounds a d hlo hhi hg
    simpa [Nat.add_comm] using h
  · have hlo : 59046 <= d := by simpa [min_eq_right hda] using hmLo
    have hhi : d <= 177143 := by simpa [min_eq_right hda] using hmHi
    have hg : absDiff (4*a) (7*d) <= 505 := by
      simpa [min_eq_right hda, max_eq_left hda] using hgap
    have h := n11_near_mass_bounds d a hlo hhi hg
    simpa [Nat.add_comm] using h

/-- Far-strip mass bounds at scale 11. -/
theorem n11_far_mass_bounds (m M : Nat)
    (hmLo : 59046 <= m) (hmHi : m <= 177143)
    (hgap : absDiff M (13*m) <= 505) :
    826139 <= m+M ∧ m+M <= 2480507 := by
  have h := absDiff_le_both M (13*m) 505 hgap
  omega

/-- Orientation-free form of the n=11 far-strip mass bounds. -/
theorem n11_far_mass_bounds_minmax (a d : Nat)
    (hmLo : 59046 <= min a d) (hmHi : min a d <= 177143)
    (hgap : absDiff (max a d) (13*min a d) <= 505) :
    826139 <= a+d ∧ a+d <= 2480507 := by
  rcases le_total a d with had | hda
  · have hlo : 59046 <= a := by simpa [min_eq_left had] using hmLo
    have hhi : a <= 177143 := by simpa [min_eq_left had] using hmHi
    have hg : absDiff d (13*a) <= 505 := by
      simpa [min_eq_left had, max_eq_right had] using hgap
    have h := n11_far_mass_bounds a d hlo hhi hg
    simpa [Nat.add_comm] using h
  · have hlo : 59046 <= d := by simpa [min_eq_right hda] using hmLo
    have hhi : d <= 177143 := by simpa [min_eq_right hda] using hmHi
    have hg : absDiff a (13*d) <= 505 := by
      simpa [min_eq_right hda, max_eq_left hda] using hgap
    have h := n11_far_mass_bounds d a hlo hhi hg
    simpa [Nat.add_comm] using h

/-- Near-strip mass bounds at scale 12. -/
theorem n12_near_mass_bounds (m M : Nat)
    (hmLo : 177144 <= m) (hmHi : m <= 531437)
    (hgap : absDiff (4*M) (7*m) <= 540) :
    487011 <= m+M ∧ m+M <= 1461586 := by
  have h := absDiff_le_both (4*M) (7*m) 540 hgap
  omega

/-- Orientation-free form of the n=12 near-strip mass bounds. -/
theorem n12_near_mass_bounds_minmax (a d : Nat)
    (hmLo : 177144 <= min a d) (hmHi : min a d <= 531437)
    (hgap : absDiff (4*max a d) (7*min a d) <= 540) :
    487011 <= a+d ∧ a+d <= 1461586 := by
  rcases le_total a d with had | hda
  · have hlo : 177144 <= a := by simpa [min_eq_left had] using hmLo
    have hhi : a <= 531437 := by simpa [min_eq_left had] using hmHi
    have hg : absDiff (4*d) (7*a) <= 540 := by
      simpa [min_eq_left had, max_eq_right had] using hgap
    have h := n12_near_mass_bounds a d hlo hhi hg
    simpa [Nat.add_comm] using h
  · have hlo : 177144 <= d := by simpa [min_eq_right hda] using hmLo
    have hhi : d <= 531437 := by simpa [min_eq_right hda] using hmHi
    have hg : absDiff (4*a) (7*d) <= 540 := by
      simpa [min_eq_right hda, max_eq_left hda] using hgap
    have h := n12_near_mass_bounds d a hlo hhi hg
    simpa [Nat.add_comm] using h

/-- Far-strip mass bounds at scale 12. -/
theorem n12_far_mass_bounds (m M : Nat)
    (hmLo : 177144 <= m) (hmHi : m <= 531437)
    (hgap : absDiff M (13*m) <= 540) :
    2479476 <= m+M ∧ m+M <= 7440658 := by
  have h := absDiff_le_both M (13*m) 540 hgap
  omega

/-- Orientation-free form of the n=12 far-strip mass bounds. -/
theorem n12_far_mass_bounds_minmax (a d : Nat)
    (hmLo : 177144 <= min a d) (hmHi : min a d <= 531437)
    (hgap : absDiff (max a d) (13*min a d) <= 540) :
    2479476 <= a+d ∧ a+d <= 7440658 := by
  rcases le_total a d with had | hda
  · have hlo : 177144 <= a := by simpa [min_eq_left had] using hmLo
    have hhi : a <= 531437 := by simpa [min_eq_left had] using hmHi
    have hg : absDiff d (13*a) <= 540 := by
      simpa [min_eq_left had, max_eq_right had] using hgap
    have h := n12_far_mass_bounds a d hlo hhi hg
    simpa [Nat.add_comm] using h
  · have hlo : 177144 <= d := by simpa [min_eq_right hda] using hmLo
    have hhi : d <= 531437 := by simpa [min_eq_right hda] using hmHi
    have hg : absDiff a (13*d) <= 540 := by
      simpa [min_eq_right hda, max_eq_left hda] using hgap
    have h := n12_far_mass_bounds d a hlo hhi hg
    simpa [Nat.add_comm] using h

/-- Exclude the n11 near cancellation strip from the blank-root orbit. -/
theorem n11_near_ratio_root_excluded (n a d : Nat)
    (hseen : run n = some (.D a d))
    (hmLo : 59046 <= min a d) (hmHi : min a d <= 177143)
    (hgap : absDiff (4*max a d) (7*min a d) <= 505) : False := by
  have hmass := n11_near_mass_bounds_minmax a d hmLo hmHi hgap
  have hnotLo : ¬ n <= 37 := by
    intro hn
    have hm := run_mass_mono n 37 a d 41468 86104 hn hseen root_run_37
    omega
  have hnotHi : ¬ 42 <= n := by
    intro hn
    have hm := run_mass_mono 42 n 22822 487342 a d hn root_run_42 hseen
    omega
  have hcases : n = 38 ∨ n = 39 ∨ n = 40 ∨ n = 41 := by omega
  rcases hcases with h38 | h39 | h40 | h41
  · subst n
    have hEq : some (.D 44634 124427) = some (.D a d) :=
      root_run_38.symm.trans hseen
    cases hEq
    have hr := absDiff_le_both (4*max 44634 124427) (7*min 44634 124427) 505 hgap
    norm_num at hr
  · subst n
    have hEq : some (.D 79788 133932) = some (.D a d) :=
      root_run_39.symm.trans hseen
    cases hEq
    have hr := absDiff_le_both (4*max 79788 133932) (7*min 79788 133932) 505 hgap
    norm_num at hr
  · subst n
    have hEq : some (.D 54138 239399) = some (.D a d) :=
      root_run_40.symm.trans hseen
    cases hEq
    have hr := absDiff_le_both (4*max 54138 239399) (7*min 54138 239399) 505 hgap
    norm_num at hr
  · subst n
    have hEq : some (.D 185262 162438) = some (.D a d) :=
      root_run_41.symm.trans hseen
    cases hEq
    have hr := absDiff_le_both (4*max 185262 162438) (7*min 185262 162438) 505 hgap
    norm_num at hr

/-- Exclude the n11 far cancellation strip from the blank-root orbit. -/
theorem n11_far_ratio_root_excluded (n a d : Nat)
    (hseen : run n = some (.D a d))
    (hmLo : 59046 <= min a d) (hmHi : min a d <= 177143)
    (hgap : absDiff (max a d) (13*min a d) <= 505) : False := by
  have hmass := n11_far_mass_bounds_minmax a d hmLo hmHi hgap
  have hnotLo : ¬ n <= 45 := by
    intro hn
    have hm := run_mass_mono n 45 a d 190506 616551 hn hseen root_run_45
    omega
  have hnotHi : ¬ 50 <= n := by
    intro hn
    have hm := run_mass_mono 50 n 613374 2088523 a d hn root_run_50 hseen
    omega
  have hcases : n = 46 ∨ n = 47 ∨ n = 48 ∨ n = 49 := by omega
  rcases hcases with h46 | h47 | h48 | h49
  · subst n
    have hEq : some (.D 426044 571540) = some (.D a d) :=
      root_run_46.symm.trans hseen
    cases hEq
    have hr := absDiff_le_both (max 426044 571540) (13*min 426044 571540) 505 hgap
    norm_num at hr
  · subst n
    have hEq : some (.D 145494 1278161) = some (.D a d) :=
      root_run_47.symm.trans hseen
    cases hEq
    have hr := absDiff_le_both (max 145494 1278161) (13*min 145494 1278161) 505 hgap
    norm_num at hr
  · subst n
    have hEq : some (.D 1132670 436504) = some (.D a d) :=
      root_run_48.symm.trans hseen
    cases hEq
    have hr := absDiff_le_both (max 1132670 436504) (13*min 1132670 436504) 505 hgap
    norm_num at hr
  · subst n
    have hEq : some (.D 696164 1309542) = some (.D a d) :=
      root_run_49.symm.trans hseen
    cases hEq
    have hr := absDiff_le_both (max 696164 1309542) (13*min 696164 1309542) 505 hgap
    norm_num at hr

/-- Exclude the n12 near cancellation strip from the blank-root orbit. -/
theorem n12_near_ratio_root_excluded (n a d : Nat)
    (hseen : run n = some (.D a d))
    (hmLo : 177144 <= min a d) (hmHi : min a d <= 531437)
    (hgap : absDiff (4*max a d) (7*min a d) <= 540) : False := by
  have hmass := n12_near_mass_bounds_minmax a d hmLo hmHi hgap
  have hnotLo : ¬ n <= 41 := by
    intro hn
    have hm := run_mass_mono n 41 a d 185262 162438 hn hseen root_run_41
    omega
  have hnotHi : ¬ 48 <= n := by
    intro hn
    have hm := run_mass_mono 48 n 1132670 436504 a d hn root_run_48 hseen
    omega
  have hcases : n = 42 ∨ n = 43 ∨ n = 44 ∨ n = 45 ∨ n = 46 ∨ n = 47 := by omega
  rcases hcases with h42 | h43 | h44 | h45 | h46 | h47
  · subst n
    have hEq : some (.D 22822 487342) = some (.D a d) :=
      root_run_42.symm.trans hseen
    cases hEq
    have hr := absDiff_le_both (4*max 22822 487342) (7*min 22822 487342) 540 hgap
    norm_num at hr
  · subst n
    have hEq : some (.D 464518 68489) = some (.D a d) :=
      root_run_43.symm.trans hseen
    cases hEq
    have hr := absDiff_le_both (4*max 464518 68489) (7*min 464518 68489) 540 hgap
    norm_num at hr
  · subst n
    have hEq : some (.D 396018 205505) = some (.D a d) :=
      root_run_44.symm.trans hseen
    cases hEq
    have hr := absDiff_le_both (4*max 396018 205505) (7*min 396018 205505) 540 hgap
    norm_num at hr
  · subst n
    have hEq : some (.D 190506 616551) = some (.D a d) :=
      root_run_45.symm.trans hseen
    cases hEq
    have hr := absDiff_le_both (4*max 190506 616551) (7*min 190506 616551) 540 hgap
    norm_num at hr
  · subst n
    have hEq : some (.D 426044 571540) = some (.D a d) :=
      root_run_46.symm.trans hseen
    cases hEq
    have hr := absDiff_le_both (4*max 426044 571540) (7*min 426044 571540) 540 hgap
    norm_num at hr
  · subst n
    have hEq : some (.D 145494 1278161) = some (.D a d) :=
      root_run_47.symm.trans hseen
    cases hEq
    have hr := absDiff_le_both (4*max 145494 1278161) (7*min 145494 1278161) 540 hgap
    norm_num at hr

/-- Exclude the n12 far cancellation strip from the blank-root orbit. -/
theorem n12_far_ratio_root_excluded (n a d : Nat)
    (hseen : run n = some (.D a d))
    (hmLo : 177144 <= min a d) (hmHi : min a d <= 531437)
    (hgap : absDiff (max a d) (13*min a d) <= 540) : False := by
  have hmass := n12_far_mass_bounds_minmax a d hmLo hmHi hgap
  have hnotLo : ¬ n <= 49 := by
    intro hn
    have hm := run_mass_mono n 49 a d 696164 1309542 hn hseen root_run_49
    omega
  have hnotHi : ¬ 55 <= n := by
    intro hn
    have hm := run_mass_mono 55 n 319702 8896323 a d hn root_run_55 hseen
    omega
  have hcases : n = 50 ∨ n = 51 ∨ n = 52 ∨ n = 53 ∨ n = 54 := by omega
  rcases hcases with h50 | h51 | h52 | h53 | h54
  · subst n
    have hEq : some (.D 613374 2088523) = some (.D a d) :=
      root_run_50.symm.trans hseen
    cases hEq
    have hr := absDiff_le_both (max 613374 2088523) (13*min 613374 2088523) 540 hgap
    norm_num at hr
  · subst n
    have hEq : some (.D 1475146 1840152) = some (.D a d) :=
      root_run_51.symm.trans hseen
    cases hEq
    have hr := absDiff_le_both (max 1475146 1840152) (13*min 1475146 1840152) 540 hgap
    norm_num at hr
  · subst n
    have hEq : some (.D 365000 4425473) = some (.D a d) :=
      root_run_52.symm.trans hseen
    cases hEq
    have hr := absDiff_le_both (max 365000 4425473) (13*min 365000 4425473) 540 hgap
    norm_num at hr
  · subst n
    have hEq : some (.D 4060470 1095032) = some (.D a d) :=
      root_run_53.symm.trans hseen
    cases hEq
    have hr := absDiff_le_both (max 4060470 1095032) (13*min 4060470 1095032) 540 hgap
    norm_num at hr
  · subst n
    have hEq : some (.D 2965430 3285134) = some (.D a d) :=
      root_run_54.symm.trans hseen
    cases hEq
    have hr := absDiff_le_both (max 2965430 3285134) (13*min 2965430 3285134) 540 hgap
    norm_num at hr

/-- Exclude the exceptional even gap-two root branch at this scale. -/
theorem n11_even_gap_two_root_excluded (n a d : Nat)
    (hseen : run n = some (.D a d))
    (hdLo : 59046 <= d) (hdHi : d <= 177143)
    (hgap : a = d+2) : False := by
  have hmassLo : 118094 <= a+d := by omega
  have hmassHi : a+d <= 354288 := by omega
  have hnotLo : ¬ n <= 36 := by
    intro hn
    have hm := run_mass_mono n 36 a d 28698 70161 hn hseen root_run_36
    omega
  have hnotHi : ¬ 42 <= n := by
    intro hn
    have hm := run_mass_mono 42 n 22822 487342 a d hn root_run_42 hseen
    omega
  have hcases : n = 37 ∨ n = 38 ∨ n = 39 ∨ n = 40 ∨ n = 41 := by omega
  rcases hcases with h37 | h38 | h39 | h40 | h41
  · subst n
    have hEq : some (.D 41468 86104) = some (.D a d) :=
      root_run_37.symm.trans hseen
    cases hEq
    omega
  · subst n
    have hEq : some (.D 44634 124427) = some (.D a d) :=
      root_run_38.symm.trans hseen
    cases hEq
    omega
  · subst n
    have hEq : some (.D 79788 133932) = some (.D a d) :=
      root_run_39.symm.trans hseen
    cases hEq
    omega
  · subst n
    have hEq : some (.D 54138 239399) = some (.D a d) :=
      root_run_40.symm.trans hseen
    cases hEq
    omega
  · subst n
    have hEq : some (.D 185262 162438) = some (.D a d) :=
      root_run_41.symm.trans hseen
    cases hEq
    omega

/-- Exclude the exceptional even gap-two root branch at this scale. -/
theorem n12_even_gap_two_root_excluded (n a d : Nat)
    (hseen : run n = some (.D a d))
    (hdLo : 177144 <= d) (hdHi : d <= 531437)
    (hgap : a = d+2) : False := by
  have hmassLo : 354290 <= a+d := by omega
  have hmassHi : a+d <= 1062876 := by omega
  have hnotLo : ¬ n <= 41 := by
    intro hn
    have hm := run_mass_mono n 41 a d 185262 162438 hn hseen root_run_41
    omega
  have hnotHi : ¬ 47 <= n := by
    intro hn
    have hm := run_mass_mono 47 n 145494 1278161 a d hn root_run_47 hseen
    omega
  have hcases : n = 42 ∨ n = 43 ∨ n = 44 ∨ n = 45 ∨ n = 46 := by omega
  rcases hcases with h42 | h43 | h44 | h45 | h46
  · subst n
    have hEq : some (.D 22822 487342) = some (.D a d) :=
      root_run_42.symm.trans hseen
    cases hEq
    omega
  · subst n
    have hEq : some (.D 464518 68489) = some (.D a d) :=
      root_run_43.symm.trans hseen
    cases hEq
    omega
  · subst n
    have hEq : some (.D 396018 205505) = some (.D a d) :=
      root_run_44.symm.trans hseen
    cases hEq
    omega
  · subst n
    have hEq : some (.D 190506 616551) = some (.D a d) :=
      root_run_45.symm.trans hseen
    cases hEq
    omega
  · subst n
    have hEq : some (.D 426044 571540) = some (.D a d) :=
      root_run_46.symm.trans hseen
    cases hEq
    omega

#print axioms n11_near_ratio_root_excluded
#print axioms n11_far_ratio_root_excluded
#print axioms n12_near_ratio_root_excluded
#print axioms n12_far_ratio_root_excluded
#print axioms n11_even_gap_two_root_excluded
#print axioms n12_even_gap_two_root_excluded

end BB6.Agent48RootMassGapN11N12
