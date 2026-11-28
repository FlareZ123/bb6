import FourRayCoupledSource
import GenericCoupledRayArithmetic

/-!
# Arbitrary-rational inverse-ray transport in the literal #623 source

This theorem composes the authentic original-source weighted drain with a
parametric algebraic transport rule. Instead of redoing eight sector
calculations for every new terminal ancestor, researchers can supply any
successor signed ray P*x ≈ Q*y and obtain a certified predecessor ray

    P*L ≈ (P+3Q)*m,

with the same depth-count coupling. Orientation swaps P and Q.
Ordinary-step, ternary-budget, and source separation hypotheses remain
explicit. Root-level discharge is a separate task.
-/

namespace BB6.Agent27GenericSourceRayTransport

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent27ThreeStepStripSource
open BB6.Agent27FourRayCoupledSource
open BB6.Agent27GenericCoupledRayArithmetic

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- A single source ordinary transition transports *any* signed rational
successor ray with uniform one-sided error control. -/
theorem ordinary_source_ray_transport (P Q N u v x y A B : Nat)
    (hhi : min u v+3<3^N)
    (hsep : min u v+N+10≤max u v)
    (hu : 0<u)
    (hord : OrdinaryStep u v x y)
    (hRayUpper : P*x≤Q*y+A)
    (hRayLower : Q*y≤P*x+B) :
    P*max u v≤(P+3*Q)*min u v+A+(P+4*Q)*N+6*P+20*Q ∧
    (P+3*Q)*min u v≤P*max u v+B+P*N+4*P+4*Q := by
  obtain ⟨r,c,hr,hcl,hcu,hx,hl,hweighted⟩ :=
    ordinary_step_coupled_envelope N u v x y hhi hsep hu hord
  exact coupled_ray_transport P Q (min u v) (max u v)
    x y N r c A B hr hcl hcu hx hl hweighted hRayUpper hRayLower

/-- Both possible source counter orientations are covered by the same
proof. This is the reusable induction step for a binary inverse-ray tree.
-/
theorem ordinary_source_pair_transport (P Q N u v x y A B : Nat)
    (hhi : min u v+3<3^N)
    (hsep : min u v+N+10≤max u v)
    (hu : 0<u)
    (hord : OrdinaryStep u v x y)
    (hPair : (P*x≤Q*y+A ∧ Q*y≤P*x+B) ∨
      (Q*x≤P*y+A ∧ P*y≤Q*x+B)) :
    (P*max u v≤(P+3*Q)*min u v+A+(P+4*Q)*N+6*P+20*Q ∧
      (P+3*Q)*min u v≤P*max u v+B+P*N+4*P+4*Q) ∨
    (Q*max u v≤(Q+3*P)*min u v+A+(Q+4*P)*N+6*Q+20*P ∧
      (Q+3*P)*min u v≤Q*max u v+B+Q*N+4*Q+4*P) := by
  obtain ⟨r,c,hr,hcl,hcu,hx,hl,hweighted⟩ :=
    ordinary_step_coupled_envelope N u v x y hhi hsep hu hord
  exact pair_of_inverse_rays P Q (min u v) (max u v)
    x y N r c A B hr hcl hcu hx hl hweighted hPair

#print axioms ordinary_source_ray_transport
#print axioms ordinary_source_pair_transport

end BB6.Agent27GenericSourceRayTransport
