import FourRayPhysicalSource

/-!
# Coupled one-sided fourth-predecessor gate for original #623

The first version projected source weighted depth and first-counter bounds
separately. Keeping the *same* successful B-drain recursion count in the
signed cancellation retains one-sided gains of 6N to 26N. The four possible
projective rays remain 40,16/13,25/4,19/7, but their narrow sides are
substantially more restrictive.

No nonhalting or universally quantified BB(6) maximality claim is made.
-/

namespace BB6.Agent27FourRayCoupledSource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent8DrainLogDepthSource
open BB6.Agent49DrainLinearLogSource
open BB6.Agent27ThreeStepStripSource
open BB6.Agent27ThreeStepStripArithmetic
open BB6.Agent27ThreeStepWeightedSource
open BB6.Agent27DrainWeightedFirstCoupledSource
open BB6.Agent27ThreeStepTightSkewSource
open BB6.Agent27ThreeStepTightSkewN13Source
open BB6.Agent27FourRayInverseConeSource
open BB6.Agent27FourRayPhysicalSource

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Retain the shared drain-depth witness when pulling the tight
two-ray gate backward: its upper error on all four rays collapses on
one side from O(27N) to O(N), O(13N), O(4N), O(7N), respectively. -/
def coupledFourRayCone (N n u v : Nat) : Prop :=
  let m := min u v
  let L := max u v
  (L ≤ 40*m+(53*N+23*n+377) ∧ 40*m ≤ L+(N+3*n+61)) ∨
  (13*L ≤ 16*m+(17*N+3*n+103) ∧ 16*m ≤ 13*L+(13*N+23*n+167)) ∨
  (4*L ≤ 25*m+(32*N+10*n+219) ∧ 25*m ≤ 4*L+(4*N+10*n+84)) ∨
  (7*L ≤ 19*m+(23*N+10*n+162) ∧ 19*m ≤ 7*L+(7*N+10*n+99))

/-- Three exact facts for each successful ordinary source branch.
The depth r in the first bound is the *same* r in the weighted equation;
c is the branch constant and belongs to {4,5,8}. -/
theorem ordinary_step_coupled_envelope (N u v x y : Nat)
    (hhi : min u v+3<3^N)
    (hsep : min u v+N+10≤max u v)
    (hord : OrdinaryStep u v x y) :
    ∃ r c : Nat, r≤N ∧ 4≤c ∧ c≤8 ∧
      x+min u v≤max u v+r+4 ∧
      max u v≤x+min u v+N+6 ∧
      2*x+y=2*max u v+min u v+c+2*r := by
  cases hord with
  | oddFar h hs =>
      have huv : v≤u := by omega
      have hb : v+3<3^N := by
        rw [Nat.min_eq_right huv] at hhi
        omega
      have ha : N+1≤u-v-5 := by
        simp only [Nat.min_eq_right huv, Nat.max_eq_left huv] at hsep
        omega
      have hbudget := large_first_has_budget N (u-v-5) (v+3) ha hb
      obtain ⟨r,hr,hup,heq⟩ :=
        drainB_weighted_depth_first_upper N (u-v-5) (v+3) 5 x y
          hbudget hb hs
      have hlo := drainB_first_lower_log N (u-v-5) (v+3) 5 x y hb hs
      refine ⟨r,4,hr,by decide,by decide,?_,?_,?_⟩
      all_goals simp only [Nat.min_eq_right huv, Nat.max_eq_left huv]
      all_goals omega
  | evenFar h hs =>
      have huv : v≤u := by omega
      have hb : v+2<3^N := by
        rw [Nat.min_eq_right huv] at hhi
        omega
      have ha : N+1≤u-v-2 := by
        simp only [Nat.min_eq_right huv, Nat.max_eq_left huv] at hsep
        omega
      have hbudget := large_first_has_budget N (u-v-2) (v+2) ha hb
      obtain ⟨r,hr,hup,heq⟩ :=
        drainB_weighted_depth_first_upper N (u-v-2) (v+2) 2 x y
          hbudget hb hs
      have hlo := drainB_first_lower_log N (u-v-2) (v+2) 2 x y hb hs
      refine ⟨r,4,hr,by decide,by decide,?_,?_,?_⟩
      all_goals simp only [Nat.min_eq_right huv, Nat.max_eq_left huv]
      all_goals omega
  | oddNear h hs =>
      have huv : u≤v := by
        by_contra hnot
        have hvu : v≤u := by omega
        simp only [Nat.min_eq_right hvu, Nat.max_eq_left hvu] at hsep
        omega
      have hb : u-1<3^N := by
        rw [Nat.min_eq_left huv] at hhi
        omega
      have ha : N+1≤v+4-u := by
        simp only [Nat.min_eq_left huv, Nat.max_eq_right huv] at hsep
        omega
      have hbudget := large_first_has_budget N (v+4-u) (u-1) ha hb
      obtain ⟨r,hr,hup,heq⟩ :=
        drainB_weighted_depth_first_upper N (v+4-u) (u-1) 3 x y
          hbudget hb hs
      have hlo := drainB_first_lower_log N (v+4-u) (u-1) 3 x y hb hs
      refine ⟨r,8,hr,by decide,by decide,?_,?_,?_⟩
      all_goals simp only [Nat.min_eq_left huv, Nat.max_eq_right huv]
      all_goals omega
  | evenNear p q d h hev hs =>
      have hb : u+1<3^N := by
        rw [Nat.min_eq_left h] at hhi
        omega
      have ha : N+1≤v+1-u := by
        simp only [Nat.min_eq_left h, Nat.max_eq_right h] at hsep
        omega
      have hbudget := large_first_has_budget N (v+1-u) (u+1) ha hb
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
      obtain ⟨r,hr,hup,heq⟩ :=
        drainB_weighted_depth_first_upper N (v+1-u) (u+1) 0 x y
          hbudget hb hbundle
      have hlo := drainB_first_lower_log N (v+1-u) (u+1) 0 x y hb hbundle
      refine ⟨r,5,hr,by decide,by decide,?_,?_,?_⟩
      all_goals simp only [Nat.min_eq_left h, Nat.max_eq_right h]
      all_goals omega

/-- All four coupled predecessor rays follow from the exact source
shared-r and c∈[4,8] envelope by linear integer arithmetic. -/
theorem tight_successor_coupled_four_ray (N n u v x y : Nat)
    (hhi : min u v+3<3^N)
    (hsep : min u v+N+10≤max u v)
    (hord : OrdinaryStep u v x y)
    (ht : tightSkew x y n) :
    coupledFourRayCone N n u v := by
  obtain ⟨r,c,hr,hcLo,hcHi,hfirst,hsecond,hpot⟩ :=
    ordinary_step_coupled_envelope N u v x y hhi hsep hord
  unfold coupledFourRayCone
  dsimp at *
  unfold tightSkew at ht
  dsimp at ht
  rcases le_total x y with hxy | hyx
  · simp only [Nat.min_eq_left hxy, Nat.max_eq_right hxy] at ht
    rcases ht with hf | hn
    · right; left
      omega
    · right; right; right
      omega
  · simp only [Nat.min_eq_right hyx, Nat.max_eq_left hyx] at ht
    rcases ht with hf | hn
    · left
      omega
    · right; right; left
      omega

/-- A genuine root successor in the tight ray forces its high-mass root
predecessor into the improved coupled four-ray cone. -/
theorem root_large_coupled_four_ray (N n t u v x y : Nat)
    (hroot : run t=some (.D u v))
    (hhi : min u v+3<3^N)
    (hlarge : 14*N+12*n+151≤min u v)
    (hs : highLevelNext (.D u v)=some (.D x y))
    (ht : tightSkew x y n) :
    coupledFourRayCone N n u v := by
  have hu : 0<u := by
    have hm := Nat.min_le_left u v
    omega
  have he := run_preserves_even t u v hroot
  have hg : u≠v+2 := by
    intro hgap
    exact large_gap_two_cannot_hit_tight N n u v x y
      hhi hlarge he hgap hs ht
  have hord := ordinary_of_step u v x y hu he hg hs
  have hfirst := ordinary_first_upper_log N u v x y hhi hord
  have hmass := BB6.Agent49ParitySource.next_strict_mass u v x y hs
  have hsecond := tight_second_upper n x y ht
  have hsep : min u v+N+10≤max u v := by
    by_contra hb
    have hminU := Nat.min_le_left u v
    have hminV := Nat.min_le_right u v
    omega
  exact tight_successor_coupled_four_ray N n u v x y hhi hsep hord ht

/-- Authenticated reachable fourth-predecessor gate at n>=13,
with improved one-sided widths and no other orbit hypotheses. -/
theorem actual_predecessor_coupled_four_ray (n t u v x y : Nat)
    (hn : 13≤n)
    (hlo : 3^(n-1)-3≤min x y)
    (hhi : min x y+3<3^n)
    (hroot : run t=some (.D u v))
    (hs : highLevelNext (.D u v)=some (.D x y))
    (ht : tightSkew x y n) :
    coupledFourRayCone (n+3) n u v := by
  have he := run_preserves_even t u v hroot
  have hsecond := even_step_second_lower u v x y he hs
  have htarget := tight_max_upper n x y ht
  have htargetY : y≤max x y := Nat.le_max_right x y
  have hgrowth := BB6.Agent27ThreeStepStripArithmetic.scale_growth n (by omega)
  have hpow : 3^(n+3)=27*3^n := by
    rw [Nat.pow_add]
    norm_num
  have hqscale : min u v+3<3^(n+3) := by omega
  have hupper := even_step_second_upper (n+3) u v x y he hqscale hs
  have hhuge := scale_growth_thirteen n hn
  have hpmin : min x y≤y := Nat.min_le_right x y
  have hqmass : 14*(n+3)+12*n+151≤min u v := by omega
  exact root_large_coupled_four_ray (n+3) n t u v x y
    hroot hqscale hqmass hs ht

/-- The original six-state blank tape, if it halts, must have a genuine
fourth high-level predecessor in one of the sharply coupled rational
rays; equivalently avoiding every such ray proves nonhalting. -/
theorem target_halt_implies_coupled_four_ray
    (hh : BusyBeaver.IsHalt target) :
    ∃ t u v n, run t=some (.D u v) ∧ 13≤n ∧
      coupledFourRayCone (n+3) n u v := by
  obtain ⟨t,x,y,n,hp,hn,hlo,hhi,ht⟩ :=
    target_halt_implies_n13_tight_skew_strip hh
  cases t with
  | zero =>
      simp only [run] at hp
      cases hp
      have hg := scale_growth_thirteen n hn
      simp at hlo
      omega
  | succ t =>
      cases hq : run t with
      | none =>
          simp [run,hq] at hp
      | some q =>
          rcases q with ⟨u,v⟩
          have hs : highLevelNext (.D u v)=some (.D x y) := by
            simpa only [run,hq,Option.bind_some] using hp
          exact ⟨t,u,v,n,hq,hn,
            actual_predecessor_coupled_four_ray n t u v x y
              hn hlo hhi hq hs ht⟩

theorem target_not_halt_of_coupled_four_ray_avoidance
    (avoid : ∀ t u v n, run t=some (.D u v) → 13≤n →
      ¬ coupledFourRayCone (n+3) n u v) :
    ¬ BusyBeaver.IsHalt target := by
  intro hh
  obtain ⟨t,u,v,n,hroot,hn,hray⟩ :=
    target_halt_implies_coupled_four_ray hh
  exact avoid t u v n hroot hn hray

#print axioms ordinary_step_coupled_envelope
#print axioms tight_successor_coupled_four_ray
#print axioms root_large_coupled_four_ray
#print axioms actual_predecessor_coupled_four_ray
#print axioms target_halt_implies_coupled_four_ray
#print axioms target_not_halt_of_coupled_four_ray_avoidance

end BB6.Agent27FourRayCoupledSource
