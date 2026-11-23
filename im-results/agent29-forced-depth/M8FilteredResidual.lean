/-!
Intermediate source-wrapper draft, not yet locally compiled or accepted by
source CI as of 2026-11-21. The underlying affineQuotientExcluded_sound
theorem is separately source-compiled and axiom-audited; this file composes
it with the second-family affine mass/scale identities.
-/

import DeepSecondFinal
import AffineQuotientExclusion
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29Depth

/-- The existing original-source M8 quotient cylinder, pulled back through
    the exact second-family affine mass identity.  This is the useful
    source-level interface for arithmetic residual filters: a root-reachable
    deep stopping input cannot satisfy the displayed parity cylinder. -/
theorem deep_root_m8_parity_exclusion_of_data
    (j m k x y d v : Nat)
    (hm : m%2=1)
    (hs : (j+m)%4=3)
    (hp : BB6.Agent15.affineNormalize (2*j+3) k = (x,y))
    (hmass : x+2*y+4*d = 2*j+3+2*k)
    (hmod : y%12=4)
    (hscale : 2^d*(y+2)=k+2)
    (hkmod : k%4=2)
    (hv : y+2=3*v)
    (hroot : BB6.Agent15.CReach (2*j+3) k) :
    ¬ (v%8=2 ∧ 2*d%4=(m+1)%4) := by
  have hy8 : y%8=4 ↔ v%8=2 := by omega
  have hx8 : x%8=7 ↔ 2*d%4=(m+1)%4 := by omega
  have hnotM8 : ¬ (x%8=7 ∧ y%8=4) := by
    intro hM8
    have hcond : BB6.Agent15.affineQuotientCondition (2*j+3) k := by
      simp [BB6.Agent15.affineQuotientCondition, hp, hM8]
    have hdec :
        decide (BB6.Agent15.affineQuotientCondition (2*j+3) k) = true :=
      decide_eq_true hcond
    have htrue :
        BB6.Agent15.affineQuotientExcluded (2*j+3) k = true := by
      unfold BB6.Agent15.affineQuotientExcluded
      simp [hdec]
    exact (BB6.Agent15.affineQuotientExcluded_sound (2*j+3) k htrue) hroot
  intro h
  exact hnotM8 ⟨hx8.mpr h.2, hy8.mpr h.1⟩

/-- For every genuine second-family stopping input in the deep sector,
    root reachability forces failure of the M8 congruence test on the exact
    affine-normalized residual.  No cutoff or sampled orbit is involved. -/
theorem second_deep_root_m8_parity_exclusion
    (j m k : Nat)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hj : j%2=0) (hm : m%2=1) (hs : (j+m)%4=3)
    (hroot : BB6.Agent15.CReach (2*j+3) k) :
    ¬ (((BB6.Agent15.affineNormalize (2*j+3) k).2+2)/3%8=2 ∧
       2*BB6.Agent15.oddDepth k%4=(m+1)%4) := by
  let p := BB6.Agent15.affineNormalize (2*j+3) k
  let x := p.1
  let y := p.2
  let d := BB6.Agent15.oddDepth k
  let v := (y+2)/3
  have hdeep := BB6.Agent15.second_halt_deep_sector j m k hstop hj hm hs
  have hp : BB6.Agent15.affineNormalize (2*j+3) k = (x,y) := by
    dsimp [x,y,p]
  have hmass : x+2*y+4*d=2*j+3+2*k := by
    simpa [x,y,d,p] using hdeep.2.2.2.1
  have hscale : 2^d*(y+2)=k+2 := by
    simpa [y,d,p] using hdeep.2.2.2.2
  have hmod : y%12=4 := by
    simpa [y,p] using
      second_deep_affine_terminal_four_mod_twelve j m k hstop hj hm hs
  have hv : y+2=3*v := by
    dsimp [v]
    omega
  have hroot' := deep_root_m8_parity_exclusion_of_data
    j m k x y d v hm hs hp hmass hmod hscale hdeep.2.1 hv hroot
  simpa [p,y,d,v] using hroot'

#print axioms deep_root_m8_parity_exclusion_of_data
#print axioms second_deep_root_m8_parity_exclusion

end BB6.Agent29Depth
