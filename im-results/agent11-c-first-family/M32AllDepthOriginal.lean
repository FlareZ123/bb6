import M32EightCells
import M32AllDepthConditional
import M32SectionEmbedding
import M32PullbackConditional
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11
open BB6.Agent15

/-- A true bridge from the original Machine C counter reachability to
    the accelerated blank-origin section: if the original M32 kernel
    proves these eight cylinders absent, every section candidate in
    those cylinders is absent at all real times. -/
theorem original_section_no_eight (x y : Nat)
    (hcell : m32Cylinder x y) : ¬ CReach x y := by
  intro h
  have hc : CCert.eightCells x y := by
    change CCert.eightCells x y at hcell
    exact hcell
  exact CCert.original_eight_unreachable x y hc
    (m32_section_reach_embeds h)

/-- Unbounded odd-depth normalization exclusions, fully source-linked to
    the original 40-block M32 quotient closure if all imported modules
    receive their standard-axiom CI audit. -/
theorem original_m32_odd_depth_barrier
    (a d q : Nat)
    (ha : a%4=3) (hq : 1≤q)
    (hmass : (a+2*(2^(d+1)*(2*q+1)-2))%32=23)
    (hclass : m32DepthClass d q) :
    ¬ CReach a (2^(d+1)*(2*q+1)-2) :=
  m32_odd_depth_reach_barrier original_section_no_eight
    a d q ha hq hmass hclass

/-- Two infinite authentic first-family stopping-index congruence
    classes become unconditional by composing the original M32
    quotient cylinder exclusions with the exact Agent3 low-gate
    and Agent15 affine source inverse grammars. -/
theorem original_m32_first_halt_two_classes (m k : Nat)
    (hm : m%2048=584 ∨ m%2048=1864)
    (hk : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  apply first_halt_m32_conditional
  · intro a b ha hb
    exact original_section_no_eight a b (Or.inl ⟨ha,hb⟩)
  · intro a b ha hb
    exact original_section_no_eight a b (Or.inr (Or.inl ⟨ha,hb⟩))
  · exact hm
  · exact hk

#print axioms original_section_no_eight
#print axioms original_m32_odd_depth_barrier
#print axioms original_m32_first_halt_two_classes
end BB6.Agent11
