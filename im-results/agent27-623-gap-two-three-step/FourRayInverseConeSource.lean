import Agent8DrainLogDepthSource
import ThreeStepStripWeightedTightSkewSource

/-!
# Four inverse ray families of the authentic #623 terminal strip

The source's exact weighted B-drain identity and one shared depth bound
transport the accepted necessary three-predecessor corridor backwards through
one *ordinary* high-level transition. This yields an explicit four-cone,
two-sided integer envelope about the rational source rays

    L/m = 40, 16/13, 25/4, 19/7.

All claims are conditional on the stated original-source ordinary transition,
a ternary input scale N and a source separation/budget condition.
They do not decide the genuine infinite blank orbit or prove #623 nonhalting.
-/

namespace BB6.Agent27FourRayInverseConeSource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent8DrainLogDepthSource
open BB6.Agent49DrainLinearLogSource
open BB6.Agent27ThreeStepStripSource
open BB6.Agent27ThreeStepWeightedSource
open BB6.Agent27DrainWeightedFirstCoupledSource
open BB6.Agent27ThreeStepTightSkewSource

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- The four possible rational preimages of the two accepted ratio strips;
we retain one-sided endpoint constants rather than symmetrizing. -/
def fourRayCone (N n u v : Nat) : Prop :=
  let m := min u v
  let L := max u v
  (L ≤ 40*m+(53*N+23*n+377) ∧ 40*m ≤ L+(27*N+3*n+88)) ∨
  (13*L ≤ 16*m+(17*N+3*n+103) ∧ 16*m ≤ 13*L+(15*N+23*n+182)) ∨
  (4*L ≤ 25*m+(32*N+10*n+219) ∧ 25*m ≤ 4*L+(18*N+10*n+102)) ∨
  (7*L ≤ 19*m+(23*N+10*n+162) ∧ 19*m ≤ 7*L+(15*N+10*n+114))

/-- Independently of orientation, at an ordinary #623 source step with
adequate ternary budget, the new first counter approximates L-m and its
second counter approximates 3m. These bounds use *the same* drain-depth
witness and original weighted conservation, not a guessed sector formula. -/
theorem ordinary_affine_envelope (N u v x y : Nat)
    (hhi : min u v+3 < 3^N)
    (hsep : min u v+N+10 ≤ max u v)
    (hord : OrdinaryStep u v x y) :
    x+min u v ≤ max u v+N+5 ∧
    max u v ≤ x+min u v+N+6 ∧
    3*min u v ≤ y+2*N+6 ∧
    y ≤ 3*min u v+4*N+20 := by
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
      have hlow := drainB_first_lower_log N (u-v-5) (v+3) 5 x y hb hs
      simp only [Nat.min_eq_right huv, Nat.max_eq_left huv]
      omega
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
      have hlow := drainB_first_lower_log N (u-v-2) (v+2) 2 x y hb hs
      simp only [Nat.min_eq_right huv, Nat.max_eq_left huv]
      omega
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
      have hlow := drainB_first_lower_log N (v+4-u) (u-1) 3 x y hb hs
      simp only [Nat.min_eq_left huv, Nat.max_eq_right huv]
      omega
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
      have hlow := drainB_first_lower_log N (v+1-u) (u+1) 0 x y hb hbundle
      simp only [Nat.min_eq_left h, Nat.max_eq_right h]
      omega

/-- If the successor lies in a genuine tight terminal corridor, its
ordinary predecessor lies in one of four narrow, explicit inverse rays.
This is a source theorem for *arbitrary* ordinary steps, not a finite census.
-/
theorem tight_successor_four_ray (N n u v x y : Nat)
    (hhi : min u v+3 < 3^N)
    (hsep : min u v+N+10 ≤ max u v)
    (hord : OrdinaryStep u v x y)
    (ht : tightSkew x y n) :
    fourRayCone N n u v := by
  obtain ⟨hxu,hxl,hyl,hyu⟩ :=
    ordinary_affine_envelope N u v x y hhi hsep hord
  unfold fourRayCone
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

/-- Explicit source-step version: whenever the actual original accelerated
transition is ordinary (for example on an even, non-gap-two blank-root
state), it obeys the four inverse rays. -/
theorem source_step_four_ray (N n u v x y : Nat)
    (hhi : min u v+3 < 3^N)
    (hsep : min u v+N+10 ≤ max u v)
    (hu : 0<u) (he : u%2=0) (hg : u≠v+2)
    (hs : highLevelNext (.D u v)=some (.D x y))
    (ht : tightSkew x y n) :
    fourRayCone N n u v :=
  tight_successor_four_ray N n u v x y hhi hsep
    (ordinary_of_step u v x y hu he hg hs) ht


/-- The first-counter upper half of the original source envelope is valid
*without* activating the ternary-ones budget. Thus it holds even close to
the diagonal, where the shared depth witness is not yet available. -/
theorem ordinary_first_upper_log (N u v x y : Nat)
    (hhi : min u v+3 < 3^N)
    (hord : OrdinaryStep u v x y) :
    x+min u v ≤ max u v+N+5 := by
  cases hord with
  | oddFar h hs =>
      have huv : v≤u := by omega
      have hb : v+3<3^N := by
        rw [Nat.min_eq_right huv] at hhi
        omega
      have hx := drainB_first_upper_log N (u-v-5) (v+3) 5 x y hb hs
      simp only [Nat.min_eq_right huv, Nat.max_eq_left huv]
      omega
  | evenFar h hs =>
      have huv : v≤u := by omega
      have hb : v+2<3^N := by
        rw [Nat.min_eq_right huv] at hhi
        omega
      have hx := drainB_first_upper_log N (u-v-2) (v+2) 2 x y hb hs
      simp only [Nat.min_eq_right huv, Nat.max_eq_left huv]
      omega
  | oddNear h hs =>
      have hb : u-1<3^N := by
        rcases le_total u v with huv | hvu
        · rw [Nat.min_eq_left huv] at hhi
          omega
        · rw [Nat.min_eq_right hvu] at hhi
          omega
      have hx := drainB_first_upper_log N (v+4-u) (u-1) 3 x y hb hs
      rcases le_total u v with huv | hvu
      · simp only [Nat.min_eq_left huv, Nat.max_eq_right huv]
        omega
      · simp only [Nat.min_eq_right hvu, Nat.max_eq_left hvu]
        omega
  | evenNear p q d h hev hs =>
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
        exact hs
      have hx := drainB_first_upper_log N (v+1-u) (u+1) 0 x y hb hbundle
      simp only [Nat.min_eq_left h, Nat.max_eq_right h]
      omega

/-- A tight terminal corridor always bounds the *second* successor
counter by thirteen times its first plus the upper signed budget, in
either orientation. -/
theorem tight_second_upper (n x y : Nat)
    (ht : tightSkew x y n) : y≤13*x+23*n+111 := by
  unfold tightSkew at ht
  dsimp at ht
  rcases le_total x y with hxy | hyx
  · simp only [Nat.min_eq_left hxy, Nat.max_eq_right hxy] at ht
    rcases ht with hf | hn <;> omega
  · omega

/-- The exact source excludes a hypothetical near-diagonal predecessor
of a terminal tight ray as soon as its minimum counter dwarfs the two
ternary depths. No assumed separation, and no unproved step recurrence. -/
theorem source_step_large_four_ray (N n u v x y : Nat)
    (hhi : min u v+3 < 3^N)
    (hlarge : 14*N+12*n+151 ≤ min u v)
    (hu : 0<u) (he : u%2=0) (hg : u≠v+2)
    (hs : highLevelNext (.D u v)=some (.D x y))
    (ht : tightSkew x y n) :
    fourRayCone N n u v := by
  have hord := ordinary_of_step u v x y hu he hg hs
  have hfirst := ordinary_first_upper_log N u v x y hhi hord
  have hmass := BB6.Agent49ParitySource.next_strict_mass u v x y hs
  have hsecond := tight_second_upper n x y ht
  have hsep : min u v+N+10 ≤ max u v := by
    by_contra hb
    have hminU : min u v≤u := Nat.min_le_left u v
    have hminV : min u v≤v := Nat.min_le_right u v
    omega
  exact tight_successor_four_ray N n u v x y hhi hsep hord ht

/-- On an exact even blank-root transition the exceptional gap-two branch
cannot produce a tight terminal corridor at the same high-mass scale.
This removes the last hypothesis needed for unconditional root transport. -/
theorem large_gap_two_cannot_hit_tight (N n u v x y : Nat)
    (hhi : min u v+3 < 3^N)
    (hlarge : 14*N+12*n+151 ≤ min u v)
    (he : u%2=0) (hg : u=v+2)
    (hs : highLevelNext (.D u v)=some (.D x y))
    (ht : tightSkew x y n) : False := by
  have h0 : u≠0 := by omega
  have h1 : ¬ (v%2=1 ∧ v+5≤u) := by omega
  have h2 : ¬ (v%2=0 ∧ v+3≤u) := by omega
  have h3 : u%2≠1 := by omega
  have hstep : drainB 0 u 2 = some (.D x y) := by
    simpa only [highLevelNext,if_neg h0,if_neg h1,if_neg h2,
      if_neg h3,if_pos hg] using hs
  have hv : v≤u := by omega
  have hb : u<3^N := by
    rw [Nat.min_eq_right hv] at hhi
    omega
  have hx := drainB_first_upper_log N 0 u 2 x y hb hstep
  have hmass := BB6.Agent49ParitySource.next_strict_mass u v x y hs
  have hsecond := tight_second_upper n x y ht
  have hminV : min u v≤v := Nat.min_le_right u v
  omega

/-- A *genuinely reached* blank-root predecessor of a tight successor
lies in one of the four rational inverse rays whenever its source
minimum counter dominates both ternary depths. In particular no assumed
near/far sector or gap-two hypothesis remains. -/
theorem root_large_four_ray (N n t u v x y : Nat)
    (hroot : run t=some (.D u v))
    (hhi : min u v+3 < 3^N)
    (hlarge : 14*N+12*n+151 ≤ min u v)
    (hs : highLevelNext (.D u v)=some (.D x y))
    (ht : tightSkew x y n) :
    fourRayCone N n u v := by
  have hu : 0<u := by
    have hm := Nat.min_le_left u v
    omega
  have he := run_preserves_even t u v hroot
  have hg : u≠v+2 := by
    intro hgap
    exact large_gap_two_cannot_hit_tight N n u v x y
      hhi hlarge he hgap hs ht
  exact source_step_large_four_ray N n u v x y
    hhi hlarge hu he hg hs ht

#print axioms ordinary_affine_envelope
#print axioms tight_successor_four_ray
#print axioms source_step_four_ray
#print axioms source_step_large_four_ray
#print axioms large_gap_two_cannot_hit_tight
#print axioms root_large_four_ray

end BB6.Agent27FourRayInverseConeSource
