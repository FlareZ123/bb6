import Q853NarrowNodes
import AffineParamRoot

namespace BB6.Agent13Narrow
open BB6.Agent13AdaptiveParam

theorem q853root0 (r : Nat) :
    (0,12*(853+P853*r)+4) ∈ BB6.Agent9Adaptive.decode r q853nodes0 := by
  apply List.mem_map.mpr
  refine ⟨(0,10240,12*P853,12), ?_, ?_⟩
  · decide
  · change (0,10240+12*P853*r)=(0,12*(853+P853*r)+4)
    simp [Nat.mul_add, Nat.mul_assoc]
    omega

theorem q853root1 (r : Nat) :
    (0,10*(853+P853*r)+4) ∈ BB6.Agent9Adaptive.decode r q853nodes1 := by
  apply List.mem_map.mpr
  refine ⟨(0,8534,10*P853,2), ?_, ?_⟩
  · decide
  · change (0,8534+10*P853*r)=(0,10*(853+P853*r)+4)
    simp [Nat.mul_add, Nat.mul_assoc]
    omega

/-- Original blank-start P1 critical-gateway exclusion for every
    q = 853 + 1024*r, equivalently n = 13650 + 16384*r. -/
theorem critical_13650_mod_16384_unreachable (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(853+P853*r)+2)-2*(16*(853+P853*r)+2)-10) := by
  exact critical_unreachable_of_affine_check
    12 11 853 P853 (by decide) (by decide)
    q853nodes0 q853nodes1 q853check0 q853check1 q853root0 q853root1 r

/-- The same finite graph proves there is no infinite feeder-0 shadow path
    anywhere in the q=853 mod 1024 cylinder. -/
theorem q853_feeder0_no_infinite_shadow_path (r : Nat) :
    ¬ Nonempty (BB6.Precision.InfiniteShadowPath
      (16*(853+P853*r)+8) (12*(853+P853*r)+4)) := by
  intro hn
  rcases hn with ⟨p⟩
  have hbound : ∀ n, p.m n ≤ 11 := by
    intro n
    exact (check_all_reach 12 11 853 8 12 P853 q853nodes0
      q853check0 q853root0 r (p.m n) (p.z n) (p.reach_all n)).1
  have hstep : ∀ n, p.m n + 1 ≤ p.m (n+1) := by
    intro n
    rw [p.hm n]
    omega
  have hmono : ∀ n, p.m 0 + n ≤ p.m n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hs := hstep n
        omega
  have hlarge := hmono 12
  have hsmall := hbound 12
  omega

/-- The same finite graph proves there is no infinite feeder-1 shadow path
    anywhere in the q=853 mod 1024 cylinder. -/
theorem q853_feeder1_no_infinite_shadow_path (r : Nat) :
    ¬ Nonempty (BB6.Precision.InfiniteShadowPath
      (16*(853+P853*r)+9) (10*(853+P853*r)+4)) := by
  intro hn
  rcases hn with ⟨p⟩
  have hbound : ∀ n, p.m n ≤ 11 := by
    intro n
    exact (check_all_reach 12 11 853 9 10 P853 q853nodes1
      q853check1 q853root1 r (p.m n) (p.z n) (p.reach_all n)).1
  have hstep : ∀ n, p.m n + 1 ≤ p.m (n+1) := by
    intro n
    rw [p.hm n]
    omega
  have hmono : ∀ n, p.m 0 + n ≤ p.m n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hs := hstep n
        omega
  have hlarge := hmono 12
  have hsmall := hbound 12
  omega

#print axioms q853_feeder0_no_infinite_shadow_path
#print axioms q853_feeder1_no_infinite_shadow_path
#print axioms critical_13650_mod_16384_unreachable
end BB6.Agent13Narrow
