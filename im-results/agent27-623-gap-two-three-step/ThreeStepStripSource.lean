import AllScaleSuccessorBoundSource
import GapTwoThreeStepSource
import ThreeStepStripArithmetic
import Agent49TerminalRatio4Source

namespace BB6.Agent27ThreeStepStripSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent49DrainLinearTerminalSource
open BB6.Agent49TerminalRatio4Source
open BB6.Agent27GapTwoThreeStepSource
open BB6.Agent27AllScaleSuccessorBoundSource
open BB6.Agent27ThreeStepStripArithmetic
open BB6.Agent8RootCorridorSource

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Exact ordinary source sectors, after removing the zero and gap-two exceptions. -/
inductive OrdinaryStep (u v x y : Nat) : Prop where
  | oddFar (h : v+5≤u) (hs : drainB (u-v-5) (v+3) 5 = some (.D x y))
  | evenFar (h : v+3≤u) (hs : drainB (u-v-2) (v+2) 2 = some (.D x y))
  | oddNear (h : u≤v+4) (hs : drainB (v+4-u) (u-1) 3 = some (.D x y))
  | evenNear (p q r : Nat) (h : u≤v)
      (he : evalA (v+1-u) u (2*u+5) = some (p,q,r))
      (hs : drainB p q r = some (.D x y))

theorem ordinary_of_step (u v x y : Nat) (hu : 0<u) (he : u%2=0)
    (hg : u≠v+2) (hs : highLevelNext (.D u v)=some (.D x y)) :
    OrdinaryStep u v x y := by
  have h0 : u≠0 := by omega
  have h3 : u%2≠1 := by omega
  by_cases h1 : v%2=1 ∧ v+5≤u
  · exact .oddFar h1.2 (by simpa only [highLevelNext,if_neg h0,if_pos h1] using hs)
  · by_cases h2 : v%2=0 ∧ v+3≤u
    · exact .evenFar h2.2 (by simpa only [highLevelNext,if_neg h0,if_neg h1,if_pos h2] using hs)
    · by_cases ho : v%2=1
      · exact .oddNear (by omega)
          (by simpa only [highLevelNext,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg hg,if_pos ho] using hs)
      · have huv : u≤v := by omega
        simp only [highLevelNext,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg hg,if_neg ho] at hs
        cases hev : evalA (v+1-u) u (2*u+5) with
        | none => simp [hev] at hs
        | some z =>
            rcases z with ⟨p,q,r⟩
            simp only [hev,Option.bind_some] at hs
            exact .evenNear p q r huv hev hs

/-- Exceptional gap-two cannot be a genuine two-step terminal parent either. -/
theorem root_terminal_parent_not_gap_two (t x y aa dd : Nat)
    (hp : run t = some (.D x y))
    (ht : highLevelNext (.D x y)=some (.D aa dd))
    (hh : highLevelNext (.D aa dd)=none) : x≠y+2 := by
  intro hg
  have hx : 32≤x := by
    by_cases h : 32≤x
    · exact h
    · exact (no_small_root_gap_two t x y hp hg (by omega)).elim
  have he := run_preserves_even t x y hp
  have hd := large_even_gap_two_exit x y aa dd hx he hg ht
  have hea := next_preserves_even x y aa dd he ht
  obtain ⟨b,e,hnext⟩ := BB6.Agent8GateRepulsionSource.right_dominated_safe aa dd hea (by omega)
  rw [hh] at hnext
  contradiction

/-- All ordinary terminal-parent sectors share one scale and one error width. -/
theorem ordinary_terminal_window (n x y aa dd : Nat)
    (hn : 10≤n) (hpos : 0<x) (hord : OrdinaryStep x y aa dd)
    (hy : y+3<3^(n+2))
    (hK : 2*(x+y+x+y+10+3*(n+2))+5<3^(n+5))
    (he : aa%2=0) (hh : highLevelNext (.D aa dd)=none) :
    (4*y≤x+9*n+38 ∧ x≤4*y+9*n+38) ∨
    (4*x≤y+9*n+38 ∧ y≤4*x+9*n+38) := by
  cases hord with
  | oddFar h hs =>
      have hw := oddFar_terminal_ratio4_source x y (n+2) (n+5) aa dd 1 5
        h (Or.inl rfl) (Or.inl rfl) hs hy he hh (by omega)
      left
      omega
  | evenFar h hs =>
      have hw := evenFar_terminal_ratio4_source x y (n+2) (n+5) aa dd 1 5
        h (Or.inl rfl) (Or.inl rfl) hs (by omega) he hh (by omega)
      left
      omega
  | oddNear h hs =>
      have hw := oddNear_terminal_ratio4_source x y (n+2) (n+5) aa dd 1 5
        hpos h (Or.inl rfl) (Or.inl rfl) hs (by omega) he hh (by omega)
      right
      omega
  | evenNear p q r h hev hs =>
      have hw := evenNear_terminal_ratio4_source x y p q r (n+2) (n+5) aa dd 1 5
        hpos h (by omega) (Or.inl rfl) (Or.inl rfl) hev hs he hh (by omega)
      right
      omega

/-- Compose each exact previous-sector gap with the terminal window. -/
theorem ordinary_previous_strip (n u v x y : Nat)
    (hn : 10≤n) (hu : 0<u)
    (hlo : 3^(n-1)-3≤min u v) (hhi : min u v+3<3^n)
    (hord : OrdinaryStep u v x y)
    (hw : (4*y≤x+9*n+38 ∧ x≤4*y+9*n+38) ∨
      (4*x≤y+9*n+38 ∧ y≤4*x+9*n+38)) : strip u v n := by
  cases hord with
  | oddFar h hs =>
      have huv : v≤u := by omega
      have hb : v+3<3^n := by simpa [Nat.min_eq_right huv] using hhi
      obtain ⟨hr,hl⟩ := oddFarGap u v x y n 1 5 h (Or.inl rfl) (Or.inl rfl) hs hb
      exact far_cancel n u v x y huv (by omega) (by omega) hw
  | evenFar h hs =>
      have huv : v≤u := by omega
      have hb : v+2<3^n := by
        rw [Nat.min_eq_right huv] at hhi
        omega
      obtain ⟨hr,hl⟩ := evenFarGap u v x y n 1 5 h (Or.inl rfl) (Or.inl rfl) hs hb
      exact far_cancel n u v x y huv (by omega) (by omega) hw
  | oddNear h hs =>
      have hb : u-1<3^n := by omega
      obtain ⟨hr,hl⟩ := oddNearGap u v x y n 1 5 hu h (Or.inl rfl) (Or.inl rfl) hs hb
      exact near_cancel n u v x y hn hlo (by omega) (by omega) hw
  | evenNear p q r h hev hs =>
      have hb : u<3^n := by
        rw [Nat.min_eq_left h] at hhi
        omega
      obtain ⟨hr,hl⟩ := evenNearGap u v p q r x y n 1 5 hu h hb
        (Or.inl rfl) (Or.inl rfl) hev hs
      exact near_cancel n u v x y hn hlo hl (by omega) hw

/-- Necessary all-scale third-predecessor condition for a genuine root terminal
chain. This conclusion is a two-strip reduction, not an orbit avoidance theorem. -/
theorem root_three_step_terminal_strip (n t u v x y aa dd : Nat)
    (hn : 10≤n) (hlo : 3^(n-1)-3≤min u v) (hhi : min u v+3<3^n)
    (hq : run t=some (.D u v))
    (hs : highLevelNext (.D u v)=some (.D x y))
    (ht : highLevelNext (.D x y)=some (.D aa dd))
    (hh : highLevelNext (.D aa dd)=none) : strip u v n := by
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
  have hw := ordinary_terminal_window n x y aa dd hn hx hordp hpy hK hea hh
  exact ordinary_previous_strip n u v x y hn hu hlo hhi hordq hw

#print axioms ordinary_of_step
#print axioms root_terminal_parent_not_gap_two
#print axioms ordinary_terminal_window
#print axioms ordinary_previous_strip
#print axioms root_three_step_terminal_strip
/-- Any section failure entails an actual root visit in one of the two
logarithmic-width strips. This removes the need to supply a terminal chain
or guess a ternary scale in the eventual root avoidance theorem. -/
theorem run_none_implies_strip (k : Nat) (hk : run k=none) :
    ∃ t u v n, run t=some (.D u v) ∧ 10≤n ∧
      3^(n-1)-3≤min u v ∧ min u v+3<3^n ∧ strip u v n := by
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
    root_three_step_terminal_strip n t u v x y aa dd hn hlo hhi hq hs ht hh⟩

/-- Complete conditional section nontermination criterion, solely a root
orbit strip-avoidance assertion. -/
theorem run_nontermination_of_strip_avoidance
    (avoid : ∀ t u v n, run t=some (.D u v) → 10≤n →
      3^(n-1)-3≤min u v → min u v+3<3^n → ¬ strip u v n) :
    ∀ k, run k≠none := by
  intro k hk
  obtain ⟨t,u,v,n,hq,hn,hlo,hhi,hstrip⟩ := run_none_implies_strip k hk
  exact avoid t u v n hq hn hlo hhi hstrip

#print axioms run_none_implies_strip
#print axioms run_nontermination_of_strip_avoidance

/-- The original blank-start machine, not merely its section evaluator,
must meet one of the two strips if it halts. -/
theorem target_halt_implies_strip (hh : BusyBeaver.IsHalt target) :
    ∃ t u v n, run t=some (.D u v) ∧ 10≤n ∧
      3^(n-1)-3≤min u v ∧ min u v+3<3^n ∧ strip u v n := by
  obtain ⟨k,hk⟩ := isHalt_iff_highLevel_acceleration.mp hh
  have hr : run k=none := by
    rw [run_eq_highLevel_iterate]
    apply Option.isNone_iff_eq_none.mp
    simpa only [highLevelStart] using hk
  exact run_none_implies_strip k hr

theorem target_not_halt_of_strip_avoidance
    (avoid : ∀ t u v n, run t=some (.D u v) → 10≤n →
      3^(n-1)-3≤min u v → min u v+3<3^n → ¬ strip u v n) :
    ¬ BusyBeaver.IsHalt target := by
  intro hh
  obtain ⟨t,u,v,n,hq,hn,hlo,hhi,hs⟩ := target_halt_implies_strip hh
  exact avoid t u v n hq hn hlo hhi hs

#print axioms target_halt_implies_strip
#print axioms target_not_halt_of_strip_avoidance

end BB6.Agent27ThreeStepStripSource
