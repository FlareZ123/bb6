import UniformInverse
import BounceReverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- The terminal even bounce for every positive uniform feeder index. -/
theorem uniform_terminal_bounce (s : Nat) (hs : 1≤s) :
    (bounce (176*s-4) (160*s)).2 = some (192*s,160*s-1) := by
  have hlo : ¬160*s<4 := by omega
  have he : ¬(176*s-4)%2=1 := by omega
  have hn4 : 160*s≠4 := by omega
  have hn5 : 160*s≠5 := by omega
  have hsmall : 160*s≤2*(176*s-4)+8 := by omega
  rw [bounce]
  simp only [hlo,ite_false,he,hn4,hn5,hsmall,ite_true,
    Option.some.injEq,Prod.mk.injEq]
  constructor
  · omega
  · trivial

/-- The exact n=2 even-bounce predecessor is a true transition for all
    positive indices. Uses the original bounce plus two proven inverse
    recursive steps, without finite simulation or a time cutoff. -/
theorem uniform_two_bounce (s : Nat) (hs : 1≤s) :
    (bounce (44*s-4) (424*s-6)).2 = some (192*s,160*s-1) := by
  have hbase := uniform_terminal_bounce s hs
  have hK1 : 2*(88*s-4)+4=176*s-4 := by omega
  have hC1 : 160*s+2*(88*s-4)+5=336*s-3 := by omega
  have hbase' : (bounce (2*(88*s-4)+4) (160*s)).2 =
      some (192*s,160*s-1) := by
    rwa [hK1]
  have hrev1 := BB6.Agent3.bounce_even_reverse (88*s-4) (160*s)
      (192*s) (160*s-1) (by omega) (by omega) hbase'
  have hone : (bounce (88*s-4) (336*s-3)).2 =
      some (192*s,160*s-1) := by
    rwa [hC1] at hrev1
  have hK0 : 2*(44*s-4)+4=88*s-4 := by omega
  have hC0 : (336*s-3)+2*(44*s-4)+5=424*s-6 := by omega
  have hone' : (bounce (2*(44*s-4)+4) (336*s-3)).2 =
      some (192*s,160*s-1) := by
    rwa [hK0]
  have hrev0 := BB6.Agent3.bounce_even_reverse (44*s-4) (336*s-3)
      (192*s) (160*s-1) (by omega) (by omega) hone'
  rwa [hC0] at hrev0

/-- A closed-form genuinely executable section edge for the n=0 branch. -/
theorem uniform_parent_zero_edge (s : Nat) (hs : 1≤s) :
    secNext (176*s-3,168*s-3)=some (192*s,160*s-1) := by
  have h0 : 176*s-3≠0 := by omega
  have h1 : 176*s-3≠1 := by omega
  have hk : 168*s-3≠0 := by omega
  have hreg : ¬2*(168*s-3)≤176*s-3 := by omega
  have hK : (176*s-3)-1=176*s-4 := by omega
  have hC : 2*(168*s-3)-(176*s-3)+3=160*s := by omega
  simp only [secNext,exactSection,if_neg h0,if_neg h1,if_neg hk,if_neg hreg]
  rw [hK,hC]
  exact uniform_terminal_bounce s hs

/-- A closed-form genuinely executable section edge for the n=2 branch. -/
theorem uniform_parent_two_edge (s : Nat) (hs : 1≤s) :
    secNext (44*s-3,234*s-6)=some (192*s,160*s-1) := by
  have h0 : 44*s-3≠0 := by omega
  have h1 : 44*s-3≠1 := by omega
  have hk : 234*s-6≠0 := by omega
  have hreg : ¬2*(234*s-6)≤44*s-3 := by omega
  have hK : (44*s-3)-1=44*s-4 := by omega
  have hC : 2*(234*s-6)-(44*s-3)+3=424*s-6 := by omega
  simp only [secNext,exactSection,if_neg h0,if_neg h1,if_neg hk,if_neg hreg]
  rw [hK,hC]
  exact uniform_two_bounce s hs

/-- True full predecessor iff, not merely the necessary inverse over-approximation. -/
theorem uniform_section_inverse_iff (s a k : Nat)
    (hs : 1≤s) (hodd : s%2=1) :
    secNext (a,k)=some (192*s,160*s-1) ↔
      (a=176*s-3 ∧ k=168*s-3) ∨
      (a=44*s-3 ∧ k=234*s-6) := by
  constructor
  · exact uniform_section_inverse s a k hs hodd
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact uniform_parent_zero_edge s hs
    · exact uniform_parent_two_edge s hs

#print axioms uniform_terminal_bounce
#print axioms uniform_two_bounce
#print axioms uniform_parent_zero_edge
#print axioms uniform_parent_two_edge
#print axioms uniform_section_inverse_iff
end BB6.Agent46
