import ScaledParameterSource
import Factor2

/-!
# Distinct scalar source parameters cannot share infinite inverse-depth streams

There is no parity restriction. The difference of any two distinct natural L
parameters has a dyadic-odd factorization. The source-margin condition on one
infinite ray and equality of initial costs suffice.
-/

namespace BB6.Agent9CrossFeeder
open BB6.Precision

/-- For any L₀ ≠ L₁, original scalar infinite shadow paths cannot have
identical depth sequences when their costs start equally and the first path
has a source margin. -/
theorem distinct_L_no_common_depth_stream
    (L0 L1 root0 root1 : Nat)
    (p0 : InfiniteShadowPath L0 root0)
    (p1 : InfiniteShadowPath L1 root1)
    (hL : 8≤L0) (hrootpos : 0<root0) (hrootmargin : root0+4≤L0)
    (hdifferent : L0≠L1)
    (hm0 : p0.m 0=p1.m 0)
    (hsame : ∀ n, p0.depth n=p1.depth n) : False := by
  let C : Int := (L1:Int)-(L0:Int)
  have hCne : C≠0 := by
    intro hzero
    dsimp [C] at hzero
    have heq : (L0:Int)=(L1:Int) := by omega
    have heqNat : L0=L1 := by exact_mod_cast heq
    exact hdifferent heqNat
  obtain ⟨e,B,hodd,hfactor⟩ := integer_odd_factor C hCne
  exact scaled_odd_parameter_no_shared_depth_stream L0 L1 root0 root1
    e B p0 p1 hL hrootpos hrootmargin hodd hfactor hm0 hsame

#print axioms distinct_L_no_common_depth_stream
end BB6.Agent9CrossFeeder
