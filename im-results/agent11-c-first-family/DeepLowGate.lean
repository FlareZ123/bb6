import AffineDepthM8
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11
open BB6.Agent15

/-- A uniform computable necessary condition on all blank-origin Machine C
    low gates with a right counter divisible by thirty-two. The criterion
    can capture arbitrarily large exact affine predecessor depths. -/
theorem low_gate_odd_u_2adic_unreachable (u : Nat)
    (hu : u%2=1)
    (hdepth : oddDepth (21*u-3)%2=0)
    (hfact : ∃ q:Nat,
      21*u-1=2^(oddDepth (21*u-3))*(8*q+6)) :
    ¬ BB6.Agent3.CReach 1 (32*u+4) := by
  have hu_pos : 1≤u := by omega
  have hgate : 32*u+4=16*(2*u)+4 := by omega
  intro hr
  rw [hgate] at hr
  obtain ⟨r,v,hv,hindex,hparent⟩ :=
    (BB6.Agent3.low_gate_all_parents_iff (2*u) (by omega)).mp hr
  have hr0 : r=0 := by
    cases r with
    | zero => rfl
    | succ n =>
      have hfac : 2*u=8*(4^n*v) := by
        calc
          2*u = 2*(4^(n+1)*v) := hindex
          _ = 2*((4^n*4)*v) := by rw [Nat.pow_succ]
          _ = (2*4)*(4^n*v) := by ac_rfl
          _ = 8*(4^n*v) := by rfl
      omega
  subst r
  have hindex2 : u=v := by omega
  subst v
  have hsub : 32*u-(11*u+3)=21*u-3 := by omega
  have hp : BB6.Agent15.CReach (22*u-3) (21*u-3) := by
    simpa [hsub] using hparent
  have ha : (22*u-3)%4=3 := by omega
  have hmass : ((22*u-3)+2*(21*u-3))%8=7 := by omega
  obtain ⟨q,hq⟩ := hfact
  have hf : ∃q:Nat, (21*u-3)+2=2^(oddDepth (21*u-3))*(8*q+6) := by
    refine ⟨q,?_⟩
    omega
  exact normalize_even_depth_m8_forbidden (22*u-3) (21*u-3)
    ha hmass hdepth hf hp

#print axioms low_gate_odd_u_2adic_unreachable
end BB6.Agent11
