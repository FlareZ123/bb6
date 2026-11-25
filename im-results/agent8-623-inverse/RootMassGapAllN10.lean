import Agent49ParitySource
import RootExclusion
import Agent8RootCancellationBudgetBridge
import Lean.Elab.Tactic.Omega

namespace BB6.Agent8RootMassGapAllN10

open BB6.Agent49ParitySource
open BB6.Agent48TerminalBudgetCounterexample
open BB6.Agent8RootCancellationBudgetBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! Source-checkpoint candidates. These are deliberately proved against the
pinned upstream highLevelNext via Agent49ParitySource.run, not via a copied
simulator. -/

theorem root_run_32 :
    run 32 = some (.D 29194 9235) := by native_decide

theorem root_run_33 :
    run 33 = some (.D 19954 27733) := by native_decide

theorem root_run_34 :
    run 34 = some (.D 7784 59872) := by native_decide

theorem root_run_35 :
    run 35 = some (.D 52084 23375) := by native_decide

theorem root_run_36 :
    run 36 = some (.D 28698 70161) := by native_decide

theorem root_run_37 :
    run 37 = some (.D 41468 86104) := by native_decide

theorem root_run_38 :
    run 38 = some (.D 44634 124427) := by native_decide

theorem root_run_42 :
    run 42 = some (.D 22822 487342) := by native_decide

theorem root_run_43 :
    run 43 = some (.D 464518 68489) := by native_decide

theorem root_run_44 :
    run 44 = some (.D 396018 205505) := by native_decide

theorem root_run_45 :
    run 45 = some (.D 190506 616551) := by native_decide

theorem root_run_46 :
    run 46 = some (.D 426044 571540) := by native_decide

/-- A 7:4 ratio strip forces total mass into the open interval
(47687,169061) throughout the n=10 scale band. -/
theorem n10_near_mass_bounds (m L : Nat)
    (hmLo : 19680 <= m) (hmHi : m <= 59045)
    (hgap : absDiff (4*L) (7*m) <= 470) :
    47687 < L+m /\ L+m < 169061 := by
  have hg := absDiff_le_both (4*L) (7*m) 470 hgap
  constructor <;> omega

/-- A 13:1 ratio strip forces total mass into the open interval
(213720,997584) throughout the n=10 scale band. -/
theorem n10_far_mass_bounds (m L : Nat)
    (hmLo : 19680 <= m) (hmHi : m <= 59045)
    (hgap : absDiff L (13*m) <= 470) :
    213720 < L+m /\ L+m < 997584 := by
  have hg := absDiff_le_both L (13*m) 470 hgap
  constructor <;> omega

/-- No genuine blank-root state in the n=10 7:4 predecessor strip.
This covers both near/far and near/near previous-ray orientations. -/
theorem n10_near_ratio_root_excluded (n a d : Nat)
    (hseen : run n = some (.D a d))
    (hmLo : 19680 <= min a d) (hmHi : min a d <= 59045)
    (hgap : absDiff (4 * max a d) (7 * min a d) <= 470) :
    False := by
  rcases le_total a d with had | hda
  · have hlo : 19680 <= a := by simpa [min_eq_left had] using hmLo
    have hhi : a <= 59045 := by simpa [min_eq_left had] using hmHi
    have hg : absDiff (4*d) (7*a) <= 470 := by
      simpa [min_eq_left had, max_eq_right had] using hgap
    have hmass := n10_near_mass_bounds a d hlo hhi hg
    have hnotlo : ¬ n < 33 := by
      intro hn
      have hm := run_mass_mono n 33 a d 19954 27733 (by omega) hseen root_run_33
      omega
    have hnotHi : ¬ 38 <= n := by
      intro hn
      have hm := run_mass_mono 38 n 44634 124427 a d hn root_run_38 hseen
      omega
    have hnot33 : n ≠ 33 := by
      intro hn
      subst n
      have hEq : some (.D 19954 27733) = some (.D a d) :=
        root_run_33.symm.trans hseen
      cases hEq
      omega
    have hcases : n = 34 ∨ n = 35 ∨ n = 36 ∨ n = 37 := by omega
    rcases hcases with h34 | h35 | h36 | h37
    · subst n
      have hEq : some (.D 7784 59872) = some (.D a d) :=
        root_run_34.symm.trans hseen
      cases hEq
      have hr := absDiff_le_both (4*59872) (7*7784) 470 hg
      omega
    · subst n
      have hEq : some (.D 52084 23375) = some (.D a d) :=
        root_run_35.symm.trans hseen
      cases hEq
      -- This exact checkpoint has the opposite coordinate ordering, so the case split itself is contradictory.
      omega
    · subst n
      have hEq : some (.D 28698 70161) = some (.D a d) :=
        root_run_36.symm.trans hseen
      cases hEq
      have hr := absDiff_le_both (4*70161) (7*28698) 470 hg
      omega
    · subst n
      have hEq : some (.D 41468 86104) = some (.D a d) :=
        root_run_37.symm.trans hseen
      cases hEq
      have hr := absDiff_le_both (4*86104) (7*41468) 470 hg
      omega
  · have hlo : 19680 <= d := by simpa [min_eq_right hda] using hmLo
    have hhi : d <= 59045 := by simpa [min_eq_right hda] using hmHi
    have hg : absDiff (4*a) (7*d) <= 470 := by
      simpa [min_eq_right hda, max_eq_left hda] using hgap
    have hmass := n10_near_mass_bounds d a hlo hhi hg
    have hnotlo : ¬ n < 33 := by
      intro hn
      have hm := run_mass_mono n 33 a d 19954 27733 (by omega) hseen root_run_33
      omega
    have hnotHi : ¬ 38 <= n := by
      intro hn
      have hm := run_mass_mono 38 n 44634 124427 a d hn root_run_38 hseen
      omega
    have hnot33 : n ≠ 33 := by
      intro hn
      subst n
      have hEq : some (.D 19954 27733) = some (.D a d) :=
        root_run_33.symm.trans hseen
      cases hEq
      omega
    have hcases : n = 34 ∨ n = 35 ∨ n = 36 ∨ n = 37 := by omega
    rcases hcases with h34 | h35 | h36 | h37
    · subst n
      have hEq : some (.D 7784 59872) = some (.D a d) :=
        root_run_34.symm.trans hseen
      cases hEq
      -- This exact checkpoint has the opposite coordinate ordering, so the case split itself is contradictory.
      omega
    · subst n
      have hEq : some (.D 52084 23375) = some (.D a d) :=
        root_run_35.symm.trans hseen
      cases hEq
      have hr := absDiff_le_both (4*52084) (7*23375) 470 hg
      omega
    · subst n
      have hEq : some (.D 28698 70161) = some (.D a d) :=
        root_run_36.symm.trans hseen
      cases hEq
      -- This exact checkpoint has the opposite coordinate ordering, so the case split itself is contradictory.
      omega
    · subst n
      have hEq : some (.D 41468 86104) = some (.D a d) :=
        root_run_37.symm.trans hseen
      cases hEq
      -- This exact checkpoint has the opposite coordinate ordering, so the case split itself is contradictory.
      omega

/-- No genuine blank-root state in the n=10 13:1 predecessor strip.
This covers both far/far and far/near previous-ray orientations. -/
theorem n10_far_ratio_root_excluded (n a d : Nat)
    (hseen : run n = some (.D a d))
    (hmLo : 19680 <= min a d) (hmHi : min a d <= 59045)
    (hgap : absDiff (max a d) (13 * min a d) <= 470) :
    False := by
  rcases le_total a d with had | hda
  · have hlo : 19680 <= a := by simpa [min_eq_left had] using hmLo
    have hhi : a <= 59045 := by simpa [min_eq_left had] using hmHi
    have hg : absDiff d (13*a) <= 470 := by
      simpa [min_eq_left had, max_eq_right had] using hgap
    have hmass := n10_far_mass_bounds a d hlo hhi hg
    have hnotlo : ¬ n < 39 := by
      intro hn
      have hm := run_mass_mono n 39 a d 79788 133932 (by omega) hseen root_run_39
      omega
    have hnotHi : ¬ 46 <= n := by
      intro hn
      have hm := run_mass_mono 46 n 426044 571540 a d hn root_run_46 hseen
      omega
    have hnot39 : n ≠ 39 := by
      intro hn
      subst n
      have hEq : some (.D 79788 133932) = some (.D a d) :=
        root_run_39.symm.trans hseen
      cases hEq
      omega
    have hcases : n = 40 ∨ n = 41 ∨ n = 42 ∨ n = 43 ∨ n = 44 ∨ n = 45 := by omega
    rcases hcases with h40 | h41 | h42 | h43 | h44 | h45
    · subst n
      have hEq : some (.D 54138 239399) = some (.D a d) :=
        root_run_40.symm.trans hseen
      cases hEq
      have hr := absDiff_le_both 239399 (13*54138) 470 hg
      omega
    · subst n
      have hEq : some (.D 185262 162438) = some (.D a d) :=
        root_run_41.symm.trans hseen
      cases hEq
      -- This exact checkpoint has the opposite coordinate ordering, so the case split itself is contradictory.
      omega
    · subst n
      have hEq : some (.D 22822 487342) = some (.D a d) :=
        root_run_42.symm.trans hseen
      cases hEq
      have hr := absDiff_le_both 487342 (13*22822) 470 hg
      omega
    · subst n
      have hEq : some (.D 464518 68489) = some (.D a d) :=
        root_run_43.symm.trans hseen
      cases hEq
      -- This exact checkpoint has the opposite coordinate ordering, so the case split itself is contradictory.
      omega
    · subst n
      have hEq : some (.D 396018 205505) = some (.D a d) :=
        root_run_44.symm.trans hseen
      cases hEq
      -- This exact checkpoint has the opposite coordinate ordering, so the case split itself is contradictory.
      omega
    · subst n
      have hEq : some (.D 190506 616551) = some (.D a d) :=
        root_run_45.symm.trans hseen
      cases hEq
      have hr := absDiff_le_both 616551 (13*190506) 470 hg
      omega
  · have hlo : 19680 <= d := by simpa [min_eq_right hda] using hmLo
    have hhi : d <= 59045 := by simpa [min_eq_right hda] using hmHi
    have hg : absDiff a (13*d) <= 470 := by
      simpa [min_eq_right hda, max_eq_left hda] using hgap
    have hmass := n10_far_mass_bounds d a hlo hhi hg
    have hnotlo : ¬ n < 39 := by
      intro hn
      have hm := run_mass_mono n 39 a d 79788 133932 (by omega) hseen root_run_39
      omega
    have hnotHi : ¬ 46 <= n := by
      intro hn
      have hm := run_mass_mono 46 n 426044 571540 a d hn root_run_46 hseen
      omega
    have hnot39 : n ≠ 39 := by
      intro hn
      subst n
      have hEq : some (.D 79788 133932) = some (.D a d) :=
        root_run_39.symm.trans hseen
      cases hEq
      omega
    have hcases : n = 40 ∨ n = 41 ∨ n = 42 ∨ n = 43 ∨ n = 44 ∨ n = 45 := by omega
    rcases hcases with h40 | h41 | h42 | h43 | h44 | h45
    · subst n
      have hEq : some (.D 54138 239399) = some (.D a d) :=
        root_run_40.symm.trans hseen
      cases hEq
      -- This exact checkpoint has the opposite coordinate ordering, so the case split itself is contradictory.
      omega
    · subst n
      have hEq : some (.D 185262 162438) = some (.D a d) :=
        root_run_41.symm.trans hseen
      cases hEq
      have hr := absDiff_le_both 185262 (13*162438) 470 hg
      omega
    · subst n
      have hEq : some (.D 22822 487342) = some (.D a d) :=
        root_run_42.symm.trans hseen
      cases hEq
      -- This exact checkpoint has the opposite coordinate ordering, so the case split itself is contradictory.
      omega
    · subst n
      have hEq : some (.D 464518 68489) = some (.D a d) :=
        root_run_43.symm.trans hseen
      cases hEq
      have hr := absDiff_le_both 464518 (13*68489) 470 hg
      omega
    · subst n
      have hEq : some (.D 396018 205505) = some (.D a d) :=
        root_run_44.symm.trans hseen
      cases hEq
      have hr := absDiff_le_both 396018 (13*205505) 470 hg
      omega
    · subst n
      have hEq : some (.D 190506 616551) = some (.D a d) :=
        root_run_45.symm.trans hseen
      cases hEq
      -- This exact checkpoint has the opposite coordinate ordering, so the case split itself is contradictory.
      omega

/-- The fifth n=10 root branch, the special even gap-two state
D(d+2,d), is also absent from the blank-root orbit. -/
theorem n10_even_gap_two_root_excluded (n d : Nat)
    (hseen : run n = some (.D (d+2) d))
    (hmin : 19680 <= d) (hmax : d <= 59045) :
    False := by
  have hlo : 39362 <= (d+2)+d := by omega
  have hhi : (d+2)+d <= 118092 := by omega
  have hnotlo : ¬ n <= 32 := by
    intro hn
    have hm := run_mass_mono n 32 (d+2) d 29194 9235 hn hseen root_run_32
    omega
  have hnotHi : ¬ 37 <= n := by
    intro hn
    have hm := run_mass_mono 37 n 41468 86104 (d+2) d hn root_run_37 hseen
    omega
  have hcases : n = 33 ∨ n = 34 ∨ n = 35 ∨ n = 36 := by omega
  rcases hcases with h33 | h34 | h35 | h36
  · subst n
    have hEq : some (.D 19954 27733) = some (.D (d+2) d) :=
      root_run_33.symm.trans hseen
    cases hEq
  · subst n
    have hEq : some (.D 7784 59872) = some (.D (d+2) d) :=
      root_run_34.symm.trans hseen
    cases hEq
  · subst n
    have hEq : some (.D 52084 23375) = some (.D (d+2) d) :=
      root_run_35.symm.trans hseen
    cases hEq
  · subst n
    have hEq : some (.D 28698 70161) = some (.D (d+2) d) :=
      root_run_36.symm.trans hseen
    cases hEq

/-- Absolute difference is symmetric. -/
theorem absDiff_comm (x y : Nat) : absDiff x y = absDiff y x := by
  unfold absDiff
  by_cases hxy : x <= y <;> by_cases hyx : y <= x <;> simp [hxy, hyx] <;> omega

/-- Convert the exact n=10 ternary scale hypotheses to their integer band. -/
theorem n10_scale_bounds (m : Nat)
    (hmin : 3^9-3 <= m) (hmax : m+3 < 3^10) :
    19680 <= m /\\ m <= 59045 := by
  norm_num at hmin hmax
  omega

/-- Full far/far terminal-to-root-ray bridge is incompatible with a
blank-root visit at n=10. -/
theorem n10_far_far_bridge_excluded (t u v x y B e c : Nat)
    (hseen : run t = some (.D u v))
    (hmin : 3^9-3 <= v) (hmax : v+3 < 3^10)
    (hB : B <= 145) (he : e <= 306) (hc : c <= 9)
    (hterm : absDiff x (4*y) <= B)
    (hbridgeLo : -(e : Int) <=
      (x : Int)-4*(y : Int)-(c : Int)-((u : Int)-13*(v : Int)))
    (hbridgeHi :
      (x : Int)-4*(y : Int)-(c : Int)-((u : Int)-13*(v : Int)) <= e) :
    False := by
  have ht := absDiff_le_both x (4*y) B hterm
  have hgapLo : -(470 : Int) <= (u : Int)-13*(v : Int) := by omega
  have hgapHi : (u : Int)-13*(v : Int) <= 470 := by omega
  have hgap := absDiff_of_int_window u (13*v) 470 hgapLo hgapHi
  have hscale := n10_scale_bounds v hmin hmax
  have hg := absDiff_le_both u (13*v) 470 hgap
  have hlarge : v <= u := by omega
  have hmLo : 19680 <= min u v := by
    simpa [min_eq_right hlarge] using hscale.1
  have hmHi : min u v <= 59045 := by
    simpa [min_eq_right hlarge] using hscale.2
  have hratio : absDiff (max u v) (13*min u v) <= 470 := by
    simpa [max_eq_left hlarge, min_eq_right hlarge] using hgap
  exact n10_far_ratio_root_excluded t u v hseen hmLo hmHi hratio

/-- Full far/near terminal-to-root-ray bridge is incompatible with a
blank-root visit at n=10. -/
theorem n10_far_near_bridge_excluded (t u v x y B e c : Nat)
    (hseen : run t = some (.D u v))
    (hmin : 3^9-3 <= u) (hmax : u+3 < 3^10)
    (hB : B <= 145) (he : e <= 306) (hc : c <= 9)
    (hterm : absDiff x (4*y) <= B)
    (hbridgeLo : -(e : Int) <=
      (x : Int)-4*(y : Int)-(c : Int)-((v : Int)-13*(u : Int)))
    (hbridgeHi :
      (x : Int)-4*(y : Int)-(c : Int)-((v : Int)-13*(u : Int)) <= e) :
    False := by
  have ht := absDiff_le_both x (4*y) B hterm
  have hgapLo : -(470 : Int) <= (v : Int)-13*(u : Int) := by omega
  have hgapHi : (v : Int)-13*(u : Int) <= 470 := by omega
  have hgap := absDiff_of_int_window v (13*u) 470 hgapLo hgapHi
  have hscale := n10_scale_bounds u hmin hmax
  have hg := absDiff_le_both v (13*u) 470 hgap
  have hlarge : u <= v := by omega
  have hmLo : 19680 <= min u v := by
    simpa [min_eq_left hlarge] using hscale.1
  have hmHi : min u v <= 59045 := by
    simpa [min_eq_left hlarge] using hscale.2
  have hratio : absDiff (max u v) (13*min u v) <= 470 := by
    simpa [max_eq_right hlarge, min_eq_left hlarge] using hgap
  exact n10_far_ratio_root_excluded t u v hseen hmLo hmHi hratio

/-- Full near/far terminal-to-root-ray bridge is incompatible with a
blank-root visit at n=10. -/
theorem n10_near_far_bridge_excluded (t u v x y B e c : Nat)
    (hseen : run t = some (.D u v))
    (hmin : 3^9-3 <= v) (hmax : v+3 < 3^10)
    (hB : B <= 145) (he : e <= 306) (hc : c <= 9)
    (hterm : absDiff y (4*x) <= B)
    (hbridgeLo : -(e : Int) <=
      (y : Int)-4*(x : Int)-(c : Int)-(7*(v : Int)-4*(u : Int)))
    (hbridgeHi :
      (y : Int)-4*(x : Int)-(c : Int)-(7*(v : Int)-4*(u : Int)) <= e) :
    False := by
  have ht := absDiff_le_both y (4*x) B hterm
  have hgapLo : -(470 : Int) <= 7*(v : Int)-4*(u : Int) := by omega
  have hgapHi : 7*(v : Int)-4*(u : Int) <= 470 := by omega
  have hgap := absDiff_of_int_window (7*v) (4*u) 470 hgapLo hgapHi
  have hscale := n10_scale_bounds v hmin hmax
  have hg := absDiff_le_both (7*v) (4*u) 470 hgap
  have hlarge : v <= u := by omega
  have hmLo : 19680 <= min u v := by
    simpa [min_eq_right hlarge] using hscale.1
  have hmHi : min u v <= 59045 := by
    simpa [min_eq_right hlarge] using hscale.2
  have hgap' : absDiff (4*u) (7*v) <= 470 := by
    rw [absDiff_comm]
    exact hgap
  have hratio : absDiff (4*max u v) (7*min u v) <= 470 := by
    simpa [max_eq_left hlarge, min_eq_right hlarge] using hgap'
  exact n10_near_ratio_root_excluded t u v hseen hmLo hmHi hratio

/-- Full near/near terminal-to-root-ray bridge is incompatible with a
blank-root visit at n=10. -/
theorem n10_near_near_bridge_excluded (t u v x y B e c : Nat)
    (hseen : run t = some (.D u v))
    (hmin : 3^9-3 <= u) (hmax : u+3 < 3^10)
    (hB : B <= 145) (he : e <= 306) (hc : c <= 9)
    (hterm : absDiff y (4*x) <= B)
    (hbridgeLo : -(e : Int) <=
      (y : Int)-4*(x : Int)-(c : Int)-(7*(u : Int)-4*(v : Int)))
    (hbridgeHi :
      (y : Int)-4*(x : Int)-(c : Int)-(7*(u : Int)-4*(v : Int)) <= e) :
    False := by
  have ht := absDiff_le_both y (4*x) B hterm
  have hgapLo : -(470 : Int) <= 7*(u : Int)-4*(v : Int) := by omega
  have hgapHi : 7*(u : Int)-4*(v : Int) <= 470 := by omega
  have hgap := absDiff_of_int_window (7*u) (4*v) 470 hgapLo hgapHi
  have hscale := n10_scale_bounds u hmin hmax
  have hg := absDiff_le_both (7*u) (4*v) 470 hgap
  have hlarge : u <= v := by omega
  have hmLo : 19680 <= min u v := by
    simpa [min_eq_left hlarge] using hscale.1
  have hmHi : min u v <= 59045 := by
    simpa [min_eq_left hlarge] using hscale.2
  have hgap' : absDiff (4*v) (7*u) <= 470 := by
    rw [absDiff_comm]
    exact hgap
  have hratio : absDiff (4*max u v) (7*min u v) <= 470 := by
    simpa [max_eq_right hlarge, min_eq_left hlarge] using hgap'
  exact n10_near_ratio_root_excluded t u v hseen hmLo hmHi hratio

#print axioms root_run_33
#print axioms root_run_34
#print axioms root_run_35
#print axioms root_run_36
#print axioms root_run_37
#print axioms root_run_38
#print axioms root_run_42
#print axioms root_run_43
#print axioms root_run_44
#print axioms root_run_45
#print axioms root_run_46
#print axioms n10_near_mass_bounds
#print axioms n10_far_mass_bounds
#print axioms n10_near_ratio_root_excluded
#print axioms n10_far_ratio_root_excluded
#print axioms root_run_32
#print axioms n10_even_gap_two_root_excluded
#print axioms absDiff_comm
#print axioms n10_scale_bounds
#print axioms n10_far_far_bridge_excluded
#print axioms n10_far_near_bridge_excluded
#print axioms n10_near_far_bridge_excluded
#print axioms n10_near_near_bridge_excluded

end BB6.Agent8RootMassGapAllN10
