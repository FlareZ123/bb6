import ThreeStepStripWeightedUltraSource
import DrainWeightedFirstCoupledSource

/-!
# One-sided #623 terminal cancellation bounds

Exact source sector constants survive the weighted-cocycle cancellation.
The first root strip is one-sided 7n+48 / 23n+114; the second is one-sided
10n+43 / 14n+67. These are necessary halting conditions for authentic
machine #623, not a root avoidance theorem or nonhalting result.
-/

namespace BB6.Agent27ThreeStepWeightedSkewSource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent22ExactDrainCocycleDepthSource
open BB6.Agent27ThreeStepStripArithmetic
open BB6.Agent27ThreeStepStripSource
open BB6.Agent27ThreeStepWeightedSource
open BB6.Agent27TerminalWindowUltraSource
open BB6.Agent27ThreeStepWeightedUltraSource
open BB6.Agent27DrainWeightedFirstCoupledSource
open BB6.Agent49DrainLinearLogSource
open BB6.Agent27GapTwoThreeStepSource
open BB6.Agent27AllScaleSuccessorBoundSource
open BB6.Agent8RootCorridorSource

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def skewStrip (u v n : Nat) : Prop :=
  let m := min u v
  let L := max u v
  (L ≤ 13*m+(23*n+114) ∧ 13*m ≤ L+(7*n+48)) ∨
  (4*L ≤ 7*m+(14*n+67) ∧ 7*m ≤ 4*L+(10*n+43))

private theorem drain_weighted_package_coupled (n a b d x y : Nat)
    (hb : b<3^n) (hbudget : b≤ternaryOnes a)
    (hs : drainB a b d=some (.D x y)) :
    ∃ r, r≤n ∧ x≤a+r ∧ a≤x+n+1 ∧
      2*x+y=2*a+d+3*b+2*r := by
  have hlo := drainB_first_lower_log n a b d x y hb hs
  obtain ⟨r,hr,hup,hEq⟩ :=
    drainB_weighted_depth_first_upper n a b d x y hbudget hb hs
  exact ⟨r,hr,hup,hlo,hEq⟩

theorem ordinary_previous_skew_strip (n u v x y : Nat)
    (hn : 10≤n) (hu : 0<u)
    (hlo : 3^(n-1)-3≤min u v) (hhi : min u v+3<3^n)
    (hord : OrdinaryStep u v x y)
    (hprior : strip u v n)
    (hw : (4*y≤x+6*n+44 ∧ x≤4*y+6*n+44) ∨
      (4*x≤y+6*n+27 ∧ y≤4*x+6*n+27)) :
    skewStrip u v n := by
  have hsep := old_strip_has_room n u v hn hlo hprior
  cases hord with
  | oddFar h hs =>
      have huv : v≤u := by omega
      have ha : n+1≤u-v-5 := by
        simp only [Nat.min_eq_right huv, Nat.max_eq_left huv] at hsep
        omega
      have hb : v+3<3^n := by
        rw [Nat.min_eq_right huv] at hhi
        omega
      have hbudget := large_first_has_budget n (u-v-5) (v+3) ha hb
      obtain ⟨r,hr,hl,hh,he⟩ :=
        drain_weighted_package_coupled n (u-v-5) (v+3) 5 x y hb hbudget hs
      unfold skewStrip
      simp only [Nat.min_eq_right huv, Nat.max_eq_left huv]
      rcases hw with hWin | hWin
      · left; omega
      · right; omega
  | evenFar h hs =>
      have huv : v≤u := by omega
      have ha : n+1≤u-v-2 := by
        simp only [Nat.min_eq_right huv, Nat.max_eq_left huv] at hsep
        omega
      have hb : v+2<3^n := by
        rw [Nat.min_eq_right huv] at hhi
        omega
      have hbudget := large_first_has_budget n (u-v-2) (v+2) ha hb
      obtain ⟨r,hr,hl,hh,he⟩ :=
        drain_weighted_package_coupled n (u-v-2) (v+2) 2 x y hb hbudget hs
      unfold skewStrip
      simp only [Nat.min_eq_right huv, Nat.max_eq_left huv]
      rcases hw with hWin | hWin
      · left; omega
      · right; omega
  | oddNear h hs =>
      have huv : u≤v := by
        by_contra hnot
        have hvu : v≤u := by omega
        simp only [Nat.min_eq_right hvu, Nat.max_eq_left hvu] at hsep
        omega
      have ha : n+1≤v+4-u := by
        simp only [Nat.min_eq_left huv, Nat.max_eq_right huv] at hsep
        omega
      have hb : u-1<3^n := by
        rw [Nat.min_eq_left huv] at hhi
        omega
      have hbudget := large_first_has_budget n (v+4-u) (u-1) ha hb
      obtain ⟨r,hr,hl,hh,he⟩ :=
        drain_weighted_package_coupled n (v+4-u) (u-1) 3 x y hb hbudget hs
      unfold skewStrip
      simp only [Nat.min_eq_left huv, Nat.max_eq_right huv]
      rcases hw with hWin | hWin
      · left; omega
      · right; omega
  | evenNear p q d h hev hs =>
      have ha : n+1≤v+1-u := by
        simp only [Nat.min_eq_left h, Nat.max_eq_right h] at hsep
        omega
      have hb : u+1<3^n := by
        rw [Nat.min_eq_left h] at hhi
        omega
      have hbudget := large_first_has_budget n (v+1-u) (u+1) ha hb
      have hq : q≤u/3 :=
        evalA_second_le_quotient (v+1-u) u (2*u+5) p q d hev
      have hqsmall : q<u+1 := by omega
      have hbundle : drainB (v+1-u) (u+1) 0 = some (.D x y) := by
        rw [drainB]
        have hne : u+1≠0 := by omega
        simp only [if_neg hne]
        have hindex : u+1-1=u := by omega
        have hthird : 0+2*(u+1)+3=2*u+5 := by omega
        rw [hindex,hthird,hev]
        simp only [Option.bind_some,if_pos hqsmall]
        exact hs
      obtain ⟨r,hr,hl,hh,he⟩ :=
        drain_weighted_package_coupled n (v+1-u) (u+1) 0 x y hb hbudget hbundle
      unfold skewStrip
      simp only [Nat.min_eq_left h, Nat.max_eq_right h]
      rcases hw with hWin | hWin
      · left; omega
      · right; omega

/-- Authentic blank-root third predecessor: the weighted-depth bound is
activated from the previously accepted coarse strip, not assumed. -/
theorem root_three_step_terminal_skew_strip (n t u v x y aa dd : Nat)
    (hn : 10≤n) (hlo : 3^(n-1)-3≤min u v) (hhi : min u v+3<3^n)
    (hq : run t=some (.D u v))
    (hs : highLevelNext (.D u v)=some (.D x y))
    (ht : highLevelNext (.D x y)=some (.D aa dd))
    (hh : highLevelNext (.D aa dd)=none) : skewStrip u v n := by
  have hprior := root_three_step_terminal_strip n t u v x y aa dd
    hn hlo hhi hq hs ht hh
  have hm := band_growth n (min u v) hn hlo
  have hu : 0<u := by omega
  have heu := run_preserves_even t u v hq
  have hgu : u≠v+2 := by
    intro hg
    exact blank_root_gap_two_no_three_step_terminal t u v x y aa dd hq hg hs ht hh
  have hordq := ordinary_of_step u v x y hu heu hgu hs
  have hp : run (t+1)=some (.D x y) := by simpa [run,hq] using hs
  have hex := run_preserves_even (t+1) x y hp
  have hea := next_preserves_even x y aa dd hex ht
  obtain ⟨hx,hodd,heven,hgate⟩ :=
    blank_root_two_step_terminal_parent_corridor (t+1) x y aa dd hp ht hh
  have hxp : x≤16*y+68 := by
    by_cases hy : y%2=1
    · have h := (hodd hy).2
      omega
    · have h := (heven (by omega)).2
      omega
  have hgy := root_terminal_parent_not_gap_two (t+1) x y aa dd hp ht hh
  have hordp := ordinary_of_step x y aa dd hx hex hgy ht
  have hy := successor_second_bound n u v x y (by omega) hhi heu hs
  obtain ⟨hpy,hK⟩ := terminal_scale n (min u v) x y hn hhi hy hxp
  have hMinU : min u v ≤ u := Nat.min_le_left u v
  have hMinV : min u v ≤ v := Nat.min_le_right u v
  have hMassStep : u+v+7≤x+y :=
    BB6.Agent49ParitySource.next_strict_mass u v x y hs
  have hMass : 200*n+600≤x+y := by omega
  have hw := ordinary_terminal_window_ultra n x y aa dd hn hx hordp hMass hpy hK hea hh
  exact ordinary_previous_skew_strip n u v x y hn hu hlo hhi hordq hprior hw

theorem run_none_implies_skew_strip (k : Nat) (hk : run k=none) :
    ∃ t u v n, run t=some (.D u v) ∧ 10≤n ∧
      3^(n-1)-3≤min u v ∧ min u v+3<3^n ∧ skewStrip u v n := by
  have hinit (j : Nat) (hj : j≤49) : ∃ s, run j=some s := by
    cases hr : run j with
    | some s => exact ⟨s,rfl⟩
    | none =>
        have hbad := run_none_forward j hr (49-j)
        rw [show j+(49-j)=49 by omega,root_run_49_small_scale] at hbad
        contradiction
  obtain ⟨t,q,p,r,hq,hs,ht,hh⟩ := terminal_chain highLevelNext run
    (fun _ => rfl) (hinit 0 (by decide)) (hinit 1 (by decide))
    (hinit 2 (by decide)) k hk
  rcases q with ⟨u,v⟩
  rcases p with ⟨x,y⟩
  rcases r with ⟨aa,dd⟩
  have hm : 19680≤min u v := by
    by_cases h : 19680≤min u v
    · exact h
    · exact (blank_root_no_small_min_three_step_terminal t u v x y aa dd
        hq (by omega) hs ht hh).elim
  obtain ⟨n,hn,hlo,hhi⟩ := scale_exists (min u v) hm
  exact ⟨t,u,v,n,hq,hn,hlo,hhi,
    root_three_step_terminal_skew_strip n t u v x y aa dd hn hlo hhi hq hs ht hh⟩

theorem target_halt_implies_skew_strip (hh : BusyBeaver.IsHalt target) :
    ∃ t u v n, run t=some (.D u v) ∧ 10≤n ∧
      3^(n-1)-3≤min u v ∧ min u v+3<3^n ∧ skewStrip u v n := by
  obtain ⟨k,hk⟩ := isHalt_iff_highLevel_acceleration.mp hh
  have hr : run k=none := by
    rw [run_eq_highLevel_iterate]
    apply Option.isNone_iff_eq_none.mp
    simpa only [highLevelStart] using hk
  exact run_none_implies_skew_strip k hr

theorem target_not_halt_of_skew_strip_avoidance
    (avoid : ∀ t u v n, run t=some (.D u v) → 10≤n →
      3^(n-1)-3≤min u v → min u v+3<3^n → ¬ skewStrip u v n) :
    ¬ BusyBeaver.IsHalt target := by
  intro hh
  obtain ⟨t,u,v,n,hq,hn,hlo,hhi,hs⟩ := target_halt_implies_skew_strip hh
  exact avoid t u v n hq hn hlo hhi hs

#print axioms old_strip_has_room
#print axioms large_first_has_budget
#print axioms drain_weighted_package
#print axioms ordinary_previous_skew_strip
#print axioms root_three_step_terminal_skew_strip
#print axioms target_halt_implies_skew_strip
#print axioms target_not_halt_of_skew_strip_avoidance

end BB6.Agent27ThreeStepWeightedSkewSource
