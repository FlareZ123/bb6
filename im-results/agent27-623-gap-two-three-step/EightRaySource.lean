import GenericSourceRayTransport

/-!
# Eight projective ancestor rays from the exact four-ray source gate

Pulling each of the four signed #623 fourth-predecessor rays backwards
through an additional successful, ordinary, budgeted original-source
transition yields exactly eight explicit necessary fifth-predecessor rays:
121, 43/40, 61/13, 55/16, 79/4, 37/25, 64/7 and 40/19.

All one-sided constants below are integer expressions derived by the
arbitrary-rational generic source transport theorem. This result is
CONDITIONAL on the earlier fourth-predecessor cone and an ordinary source
fifth-to-fourth step with strong budget and separation. It does not
assert the real blank orbit satisfies those prerequisites or prove a halt
decision. The authentic blank-root bridge is supplied in FifthRayPhysicalSource; it retains a derived root-scale interval, and its end-to-end source acceptance is a separate CI target.
-/

namespace BB6.Agent27EightRaySource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent27ThreeStepStripSource
open BB6.Agent27FourRayCoupledSource
open BB6.Agent27GenericSourceRayTransport

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Explicit coupled inverse-image cone for any ordinary predecessor of
the source-certified four-ray necessary terminal condition. -/
def eightRayCone (N n u v : Nat) : Prop :=
  let m := min u v
  let L := max u v
  ((1*L≤121*m+(214*N+23*n+1183) ∧ 121*m≤1*L+(2*N+3*n+225)) ∨
    (40*L≤43*m+(45*N+3*n+321) ∧ 43*m≤40*L+(93*N+23*n+541))) ∨
  ((13*L≤61*m+(94*N+3*n+501) ∧ 61*m≤13*L+(26*N+23*n+283)) ∨
    (16*L≤55*m+(81*N+23*n+523) ∧ 55*m≤16*L+(33*N+3*n+219))) ∨
  ((4*L≤79*m+(136*N+10*n+743) ∧ 79*m≤4*L+(8*N+10*n+200)) ∨
    (25*L≤37*m+(45*N+10*n+314) ∧ 37*m≤25*L+(57*N+10*n+335))) ∨
  ((7*L≤64*m+(106*N+10*n+584) ∧ 64*m≤7*L+(14*N+10*n+203)) ∨
    (19*L≤40*m+(54*N+10*n+353) ∧ 40*m≤19*L+(42*N+10*n+266)))

/-- A general original-source one-step preimage of a four-ray successor
satisfies one of the eight explicit one-sided rational cones. -/
theorem ordinary_four_to_eight (N n u v x y : Nat)
    (hhi : min u v+3<3^N)
    (hsep : min u v+N+10≤max u v)
    (hu : 0<u)
    (hord : OrdinaryStep u v x y)
    (ht : coupledFourRayCone N n x y) :
    eightRayCone N n u v := by
  unfold coupledFourRayCone at ht
  dsimp at ht
  unfold eightRayCone
  dsimp
  rcases le_total x y with hxy | hyx
  · simp only [Nat.min_eq_left hxy,Nat.max_eq_right hxy] at ht
    rcases ht with h1 | h2 | h3 | h4
    · have htransport := ordinary_source_ray_transport
        40 1 N u v x y (N+3*n+61) (53*N+23*n+377)
        hhi hsep hu hord (by simpa using h1.2) h1.1
      left
      right
      constructor <;> omega
    · have htransport := ordinary_source_ray_transport
        16 13 N u v x y (13*N+23*n+167) (17*N+3*n+103)
        hhi hsep hu hord h2.2 h2.1
      right
      left
      right
      constructor <;> omega
    · have htransport := ordinary_source_ray_transport
        25 4 N u v x y (4*N+10*n+84) (32*N+10*n+219)
        hhi hsep hu hord h3.2 h3.1
      right
      right
      left
      right
      constructor <;> omega
    · have htransport := ordinary_source_ray_transport
        19 7 N u v x y (7*N+10*n+99) (23*N+10*n+162)
        hhi hsep hu hord h4.2 h4.1
      right
      right
      right
      right
      constructor <;> omega
  · simp only [Nat.min_eq_right hyx,Nat.max_eq_left hyx] at ht
    rcases ht with h1 | h2 | h3 | h4
    · have htransport := ordinary_source_ray_transport
        1 40 N u v x y (53*N+23*n+377) (N+3*n+61)
        hhi hsep hu hord h1.1 (by simpa using h1.2)
      left
      left
      constructor <;> omega
    · have htransport := ordinary_source_ray_transport
        13 16 N u v x y (17*N+3*n+103) (13*N+23*n+167)
        hhi hsep hu hord h2.1 h2.2
      right
      left
      left
      constructor <;> omega
    · have htransport := ordinary_source_ray_transport
        4 25 N u v x y (32*N+10*n+219) (4*N+10*n+84)
        hhi hsep hu hord h3.1 h3.2
      right
      right
      left
      left
      constructor <;> omega
    · have htransport := ordinary_source_ray_transport
        7 19 N u v x y (23*N+10*n+162) (7*N+10*n+99)
        hhi hsep hu hord h4.1 h4.2
      right
      right
      right
      left
      constructor <;> omega

#print axioms ordinary_four_to_eight

end BB6.Agent27EightRaySource
