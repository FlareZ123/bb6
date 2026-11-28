import EightRaySource

/-!
# A fifth predecessor is genuinely reached if original six-state #623 halts

This source-level reduction removes the previously conditional *one more
step* of the eight-ray inverse construction: at n>=13 the genuine source
third predecessor is so massive that both previous genuine inputs
automatically have enough ternary room and cannot be exceptional
gap-two or near-diagonal transitions. It also transports a lower scale
bound 3^(n-4)<=min(u,v) to the fifth predecessor, so the ray parameter
cannot be inflated independently of a fixed root state. Hence a halting
authentic blank machine must reach one of eight explicit fifth-predecessor
cones at its own scale.

This is a source proof CANDIDATE until pinned upstream CI accepts it.
The resulting eight cones remain *necessary* halting conditions, not
an all-time root-avoidance theorem or a BB(6) maximality certificate.
-/

namespace BB6.Agent27FifthRayPhysicalSource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent49DrainLinearLogSource
open BB6.Agent27ThreeStepStripSource
open BB6.Agent27ThreeStepStripArithmetic
open BB6.Agent27ThreeStepTightSkewSource
open BB6.Agent27ThreeStepTightSkewN13Source
open BB6.Agent27FourRayInverseConeSource
open BB6.Agent27FourRayPhysicalSource
open BB6.Agent27FourRayCoupledSource
open BB6.Agent27EightRaySource

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- A large *reached* successor first counter prevents every exceptional
or near-diagonal sector of the original even-first source step, as soon
as the predecessor has positive minimum and an input ternary scale. -/
theorem root_big_first_forces_ordinary_separated
    (N t u v x y : Nat)
    (hroot : run t=some (.D u v))
    (hmin : 0<min u v)
    (hhi : min u v+3<3^N)
    (hxlarge : 2*N+15≤x)
    (hs : highLevelNext (.D u v)=some (.D x y)) :
    OrdinaryStep u v x y ∧ min u v+N+10≤max u v := by
  have hu : 0<u := by
    have hm := Nat.min_le_left u v
    omega
  have he := run_preserves_even t u v hroot
  have hgap : u≠v+2 := by
    intro hg
    have hv : v≤u := by omega
    have hb : u<3^N := by
      rw [Nat.min_eq_right hv] at hhi
      omega
    have h1 : ¬ (v%2=1 ∧ v+5≤u) := by omega
    have h2 : ¬ (v%2=0 ∧ v+3≤u) := by omega
    have h3 : u%2≠1 := by omega
    have hneq : u≠0 := by omega
    have hd : drainB 0 u 2=some (.D x y) := by
      simpa only [highLevelNext,if_neg hneq,if_neg h1,
        if_neg h2,if_neg h3,if_pos hg] using hs
    have hx := drainB_first_upper_log N 0 u 2 x y hb hd
    omega
  have hord := ordinary_of_step u v x y hu he hgap hs
  have hfirst := ordinary_first_upper_log N u v x y hhi hord
  constructor
  · exact hord
  · omega

/-- A genuine halt forces one of the eight explicit rational fifth-
predecessor cones, with a scale interval transported to the authentic
root state. The lower bound prevents the ray parameter from being chosen
arbitrarily large at a fixed state. -/
theorem target_halt_implies_eight_ray
    (hh : BusyBeaver.IsHalt target) :
    ∃ t u v n, run t=some (.D u v) ∧ 13≤n ∧
      3^(n-4)≤min u v ∧ min u v+3<3^(n+3) ∧
      eightRayCone (n+3) n u v := by
  obtain ⟨tp,px,py,n,hp,hn,hlo,hhi,ht⟩ :=
    target_halt_implies_n13_tight_skew_strip hh
  have hgrowth := scale_growth_thirteen n hn
  have hminLarge : 1000*n+997≤min px py := by omega
  have hmaxp := tight_max_upper n px py ht
  have hsumP : px+py=max px py+min px py := by
    rcases le_total px py with hxy | hyx
    · simp only [Nat.max_eq_right hxy,Nat.min_eq_left hxy]
      omega
    · simp only [Nat.max_eq_left hyx,Nat.min_eq_right hyx]
      omega
  have hscale := scale_growth n (by omega)
  have hpow : 3^(n+3)=27*3^n := by
    rw [Nat.pow_add]
    omega
  have hpMass : px+py<3^(n+3) := by omega
  cases tp with
  | zero =>
      simp only [run] at hp
      cases hp
      simp at hlo
      omega
  | succ tq =>
      cases hq : run tq with
      | none =>
          simp [run,hq] at hp
      | some s =>
          rcases s with ⟨qx,qy⟩
          have hstepQ : highLevelNext (.D qx qy)=some (.D px py) := by
            simpa only [run,hq,Option.bind_some] using hp
          have hmassQ := BB6.Agent49ParitySource.next_strict_mass
            qx qy px py hstepQ
          have hscaleQ : min qx qy+3<3^(n+3) := by
            have hm := Nat.min_le_left qx qy
            omega
          have heQ := run_preserves_even tq qx qy hq
          have hyQ := even_step_second_upper (n+3) qx qy px py
            heQ hscaleQ hstepQ
          have hqMinLarge : 20*(n+3)+100≤min qx qy := by
            have hpminY := Nat.min_le_right px py
            omega
          have hfour := actual_predecessor_coupled_four_ray
            n tq qx qy px py hn hlo hhi hq hstepQ ht
          cases tq with
          | zero =>
              simp only [run] at hq
              cases hq
              omega
          | succ tr =>
              cases hr : run tr with
              | none =>
                  simp [run,hr] at hq
              | some s =>
                  rcases s with ⟨ru,rv⟩
                  have hstepR :
                      highLevelNext (.D ru rv)=some (.D qx qy) := by
                    simpa only [run,hr,Option.bind_some] using hq
                  have hmassR := BB6.Agent49ParitySource.next_strict_mass
                    ru rv qx qy hstepR
                  have hscaleR : min ru rv+3<3^(n+3) := by
                    have hm := Nat.min_le_left ru rv
                    omega
                  have heR := run_preserves_even tr ru rv hr
                  have hyR := even_step_second_upper (n+3)
                    ru rv qx qy heR hscaleR hstepR
                  have hminP := Nat.min_le_right px py
                  have hminQ := Nat.min_le_right qx qy
                  have hmassBound : 3^(n-1) ≤ 9*min ru rv+16*(n+3)+83 := by
                    omega
                  have hpow3 : 3^(n-1)=27*3^(n-4) := by
                    have hn' : n-1=n-4+3 := by omega
                    rw [hn',Nat.pow_add]
                    norm_num
                  have hscaleBudget : 16*(n+3)+83≤18*3^(n-4) := by
                    have hbase : 1000*n+1000≤3^(n-1) := by omega
                    rw [hpow3] at hbase
                    omega
                  have hminRLower : 3^(n-4)≤min ru rv := by
                    rw [hpow3] at hmassBound
                    omega
                  have hminR : 0<min ru rv := by
                    have hm := Nat.min_le_right qx qy
                    omega
                  have hqxLarge : 2*(n+3)+15≤qx := by
                    have hm := Nat.min_le_left qx qy
                    omega
                  obtain ⟨hord,hsep⟩ :=
                    root_big_first_forces_ordinary_separated
                      (n+3) tr ru rv qx qy hr hminR
                      hscaleR hqxLarge hstepR
                  exact ⟨tr,ru,rv,n,hr,hn,hminRLower,hscaleR,
                    ordinary_four_to_eight (n+3) n ru rv qx qy
                      hscaleR hsep hord hfour⟩

/-- This is an exact conditional nonhalting reduction at eight source
rays. Establishing the all-time root avoidance premise remains open. -/
theorem target_not_halt_of_eight_ray_avoidance
    (avoid : ∀ t u v n, run t=some (.D u v) → 13≤n →
      3^(n-4)≤min u v → min u v+3<3^(n+3) →
      ¬ eightRayCone (n+3) n u v) :
    ¬ BusyBeaver.IsHalt target := by
  intro hh
  obtain ⟨t,u,v,n,hroot,hn,hscaleLo,hscaleHi,height⟩ :=
    target_halt_implies_eight_ray hh
  exact avoid t u v n hroot hn hscaleLo hscaleHi height

#print axioms root_big_first_forces_ordinary_separated
#print axioms target_halt_implies_eight_ray
#print axioms target_not_halt_of_eight_ray_avoidance

end BB6.Agent27FifthRayPhysicalSource
