import FourRayInverseConeSource
import ThreeStepStripWeightedTightSkewN13Source

/-!
# Four-predecessor necessary rays for the genuine six-state #623 blank start

A fourth predecessor is guaranteed for any genuinely halting blank-root
orbit. No auxiliary separation or budget assumptions remain: the relevant
ternary scale for the predecessor is forced by the mass and final tight
terminal corridor. Its four possible rational rays are 40,16/13,25/4,19/7.
This theorem is a necessary halting restriction, not a nonhalting proof.
-/

namespace BB6.Agent27FourRayPhysicalSource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent49DrainLinearLogSource
open BB6.Agent27ThreeStepStripSource
open BB6.Agent27ThreeStepStripArithmetic
open BB6.Agent27ThreeStepWeightedSource
open BB6.Agent27ThreeStepTightSkewSource
open BB6.Agent27ThreeStepTightSkewN13Source
open BB6.Agent27FourRayInverseConeSource

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Any natural block count is smaller than 3 to its own power. -/
private theorem block_lt_ternary_power (b : Nat) : b<3^b := by
  induction b with
  | zero => decide
  | succ b ih =>
      rw [Nat.pow_succ]
      omega

private theorem drain_first_le_a_plus_b
    (a b d x y : Nat) (hs : drainB a b d=some (.D x y)) :
    x≤a+b :=
  drainB_first_upper_log b a b d x y (block_lt_ternary_power b) hs

private theorem ordinary_first_unscaled (u v x y : Nat)
    (hu : 0<u) (hord : OrdinaryStep u v x y) :
    x≤max u v+3 := by
  cases hord with
  | oddFar h hs =>
      have huv : v≤u := by omega
      have hx := drain_first_le_a_plus_b (u-v-5) (v+3) 5 x y hs
      simp only [Nat.max_eq_left huv]
      omega
  | evenFar h hs =>
      have huv : v≤u := by omega
      have hx := drain_first_le_a_plus_b (u-v-2) (v+2) 2 x y hs
      simp only [Nat.max_eq_left huv]
      omega
  | oddNear h hs =>
      have hx := drain_first_le_a_plus_b (v+4-u) (u-1) 3 x y hs
      rcases le_total u v with huv | hvu
      · simp only [Nat.max_eq_right huv]
        omega
      · simp only [Nat.max_eq_left hvu]
        omega
  | evenNear p q d h hev hs =>
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
      have hx := drain_first_le_a_plus_b (v+1-u) (u+1) 0 x y hbundle
      simp only [Nat.max_eq_right h]
      omega

/-- Every successful actual even source step has first output bounded
above by the old maximum plus three, with no ternary-scale hypothesis.
The zero and gap-two branches are included. -/
theorem even_step_first_unscaled (u v x y : Nat)
    (he : u%2=0)
    (hs : highLevelNext (.D u v)=some (.D x y)) :
    x≤max u v+3 := by
  by_cases hzero : u=0
  · by_cases hv : v%2=1
    · have hd : drainB (v+1) 2 2=some (.D x y) := by
        simpa only [highLevelNext,if_pos hzero,if_pos hv] using hs
      have hx := drain_first_le_a_plus_b (v+1) 2 2 x y hd
      simp [hzero]
      omega
    · have hp : some (.D v 7)=some (.D x y) := by
        simpa only [highLevelNext,if_pos hzero,if_neg hv] using hs
      cases hp
      simp [hzero]
  · by_cases hg : u=v+2
    · have h1 : ¬ (v%2=1 ∧ v+5≤u) := by omega
      have h2 : ¬ (v%2=0 ∧ v+3≤u) := by omega
      have h3 : u%2≠1 := by omega
      have hd : drainB 0 u 2=some (.D x y) := by
        simpa only [highLevelNext,if_neg hzero,if_neg h1,
          if_neg h2,if_neg h3,if_pos hg] using hs
      have hx := drain_first_le_a_plus_b 0 u 2 x y hd
      have hv : v≤u := by omega
      simpa only [Nat.max_eq_left hv] using
        (show x≤u+3 by omega)
    · exact ordinary_first_unscaled u v x y (by omega)
        (ordinary_of_step u v x y (by omega) he hg hs)

/-- Strict source mass growth and the globally bounded first counter
force the successor's second coordinate to exceed the predecessor minimum. -/
theorem even_step_second_lower (u v x y : Nat)
    (he : u%2=0)
    (hs : highLevelNext (.D u v)=some (.D x y)) :
    min u v+4≤y := by
  have hx := even_step_first_unscaled u v x y he hs
  have hm := BB6.Agent49ParitySource.next_strict_mass u v x y hs
  rcases le_total u v with huv | hvu
  · simp only [Nat.min_eq_left huv, Nat.max_eq_right huv] at *
    omega
  · simp only [Nat.min_eq_right hvu, Nat.max_eq_left hvu] at *
    omega

/-- Terminal two-strip alternatives bound either successor orientation
by a uniform 13:1 maximum. -/
theorem tight_max_upper (n x y : Nat) (ht : tightSkew x y n) :
    max x y≤13*min x y+23*n+111 := by
  unfold tightSkew at ht
  dsimp at ht
  rcases ht with hf | hn
  · exact hf.1
  · omega

/-- For an even source input, the second coordinate of a *successful*
next state is at most 3 times the old minimum plus a logarithmic
correction. No prior large-separation assumption is made. -/
theorem even_step_second_upper (N u v x y : Nat)
    (he : u%2=0)
    (hhi : min u v+3<3^N)
    (hs : highLevelNext (.D u v)=some (.D x y)) :
    y≤3*min u v+4*N+20 := by
  by_cases hzero : u=0
  · by_cases hv : v%2=1
    · have hd : drainB (v+1) 2 2=some (.D x y) := by
        simpa only [highLevelNext,if_pos hzero,if_pos hv] using hs
      have hb : 2<3^N := by
        simp [hzero] at hhi
        omega
      have hy := drainB_upper_linear_log N (v+1) 2 2 x y hb hd
      simp [hzero]
      omega
    · have hp : some (.D v 7)=some (.D x y) := by
        simpa only [highLevelNext,if_pos hzero,if_neg hv] using hs
      cases hp
      simp [hzero]
  · by_cases hg : u=v+2
    · have h1 : ¬ (v%2=1 ∧ v+5≤u) := by omega
      have h2 : ¬ (v%2=0 ∧ v+3≤u) := by omega
      have h3 : u%2≠1 := by omega
      have hd : drainB 0 u 2=some (.D x y) := by
        simpa only [highLevelNext,if_neg hzero,if_neg h1,
          if_neg h2,if_neg h3,if_pos hg] using hs
      have hv : v≤u := by omega
      have hb : u<3^N := by
        rw [Nat.min_eq_right hv] at hhi
        omega
      have hy := drainB_upper_linear_log N 0 u 2 x y hb hd
      simp only [Nat.min_eq_right hv]
      omega
    · have hord := ordinary_of_step u v x y (by omega) he hg hs
      cases hord with
      | oddFar h hd =>
          have hv : v≤u := by omega
          have hb : v+3<3^N := by
            rw [Nat.min_eq_right hv] at hhi
            omega
          have hy := drainB_upper_linear_log N (u-v-5) (v+3) 5 x y hb hd
          simp only [Nat.min_eq_right hv]
          omega
      | evenFar h hd =>
          have hv : v≤u := by omega
          have hb : v+2<3^N := by
            rw [Nat.min_eq_right hv] at hhi
            omega
          have hy := drainB_upper_linear_log N (u-v-2) (v+2) 2 x y hb hd
          simp only [Nat.min_eq_right hv]
          omega
      | oddNear h hd =>
          have hb : u-1<3^N := by
            rcases le_total u v with huv | hvu
            · rw [Nat.min_eq_left huv] at hhi
              omega
            · rw [Nat.min_eq_right hvu] at hhi
              omega
          have hy := drainB_upper_linear_log N (v+4-u) (u-1) 3 x y hb hd
          rcases le_total u v with huv | hvu
          · simp only [Nat.min_eq_left huv]
            omega
          · simp only [Nat.min_eq_right hvu]
            omega
      | evenNear p q d h hev hd =>
          have hb : u+1<3^N := by
            rw [Nat.min_eq_left h] at hhi
            omega
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
            exact hd
          have hy := drainB_upper_linear_log N (v+1-u) (u+1) 0 x y hb hbundle
          simp only [Nat.min_eq_left h]
          omega

/-- A stronger than linear source ternary band inequality, beginning at
depth 13. It is elementary induction on the power, not a simulation. -/
theorem scale_growth_thirteen (n : Nat) (hn : 13≤n) :
    1000*n+1000≤3^(n-1) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => decide
  | succ k ih =>
      have hp : 3^(13+(k+1)-1)=3*3^(13+k-1) := by
        have hidx : 13+(k+1)-1=(13+k-1)+1 := by omega
        rw [hidx,Nat.pow_succ]
        omega
      omega

/-- A reached third predecessor obeying the necessary tight corridor
has a fourth predecessor in the four-ray cone automatically, at the
explicit source depth N=n+3. The predecessor counter scale and large-gap
hypotheses are discharged from authentic mass growth, without guessing
or assuming either one. -/
theorem actual_predecessor_four_ray (n t u v x y : Nat)
    (hn : 13≤n)
    (hlo : 3^(n-1)-3≤min x y)
    (hhi : min x y+3<3^n)
    (hq : run t=some (.D u v))
    (hs : highLevelNext (.D u v)=some (.D x y))
    (ht : tightSkew x y n) :
    fourRayCone (n+3) n u v := by
  have he := run_preserves_even t u v hq
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
  exact root_large_four_ray (n+3) n t u v x y hq
    hqscale hqmass hs ht

/-- Unconditional original blank six-state machine halting forces an
authentic reached *fourth* predecessor inside one of four affine rays,
at a ternary depth n>=13. The original blank-machine bridge is inherited
from the source-certified three-predecessor theorem. -/
theorem target_halt_implies_four_ray (hh : BusyBeaver.IsHalt target) :
    ∃ t u v n, run t=some (.D u v) ∧ 13≤n ∧
      fourRayCone (n+3) n u v := by
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
            actual_predecessor_four_ray n t u v x y hn hlo hhi hq hs ht⟩

/-- A small collection of four source rays is the only remaining
four-predecessor halting obstruction. This is a conditional reduction,
not a claim that the avoidance hypothesis has been established. -/
theorem target_not_halt_of_four_ray_avoidance
    (avoid : ∀ t u v n, run t=some (.D u v) → 13≤n →
      ¬ fourRayCone (n+3) n u v) :
    ¬ BusyBeaver.IsHalt target := by
  intro hh
  obtain ⟨t,u,v,n,hq,hn,hray⟩ := target_halt_implies_four_ray hh
  exact avoid t u v n hq hn hray

#print axioms even_step_first_unscaled
#print axioms even_step_second_lower
#print axioms tight_max_upper
#print axioms even_step_second_upper
#print axioms scale_growth_thirteen
#print axioms actual_predecessor_four_ray
#print axioms target_halt_implies_four_ray
#print axioms target_not_halt_of_four_ray_avoidance

end BB6.Agent27FourRayPhysicalSource
