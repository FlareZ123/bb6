import AffineTarget
import Lean.Elab.Tactic.Omega
namespace BB6.Agent46

/-- The depth-zero even bounce is a genuine precursor for each affine target. -/
private theorem bounce_target_terminal (q : Nat) :
    (bounce (352*q+84) (320*q+80)).2 = some (384*q+96,320*q+79) := by
  rw [bounce]
  have hlarge : ¬(320*q+80<4) := by omega
  have heven : (352*q+84)%2≠1 := by omega
  have hn4 : 320*q+80≠4 := by omega
  have hn5 : 320*q+80≠5 := by omega
  have hsmall : 320*q+80≤2*(352*q+84)+8 := by omega
  simp only [hlarge,ite_false,heven,hn4,hn5,hsmall,ite_true,
    Prod.snd, Option.some.injEq, Prod.mk.injEq]
  omega

/-- The two-level even bounce is a second genuine affine precursor. -/
private theorem bounce_target_twice (q : Nat) :
    (bounce (88*q+18) (848*q+206)).2 = some (384*q+96,320*q+79) := by
  rw [bounce]
  have hlarge : ¬(848*q+206<4) := by omega
  have heven : (88*q+18)%2≠1 := by omega
  have hn4 : 848*q+206≠4 := by omega
  have hn5 : 848*q+206≠5 := by omega
  have hsmall : ¬(848*q+206≤2*(88*q+18)+8) := by omega
  simp only [hlarge,ite_false,heven,hn4,hn5,hsmall]
  have heqK : 2*(88*q+18)+4=176*q+40 := by omega
  have heqC : 848*q+206-(2*(88*q+18)+5)=672*q+165 := by omega
  rw [heqK,heqC]
  rw [bounce]
  have hlarge2 : ¬(672*q+165<4) := by omega
  have heven2 : (176*q+40)%2≠1 := by omega
  have hn42 : 672*q+165≠4 := by omega
  have hn52 : 672*q+165≠5 := by omega
  have hsmall2 : ¬(672*q+165≤2*(176*q+40)+8) := by omega
  simp only [hlarge2,ite_false,heven2,hn42,hn52,hsmall2]
  have heqK2 : 2*(176*q+40)+4=352*q+84 := by omega
  have heqC2 : 672*q+165-(2*(176*q+40)+5)=320*q+80 := by omega
  rw [heqK2,heqC2]
  exact bounce_target_terminal q

/-- Both families of source predecessors are genuine exact section edges. -/
private theorem first_parent_outputs_target (q : Nat) :
    secNext (352*q+85,336*q+81) = some (384*q+96,320*q+79) := by
  have h0 : 352*q+85≠0 := by omega
  have h1 : 352*q+85≠1 := by omega
  have hk0 : 336*q+81≠0 := by omega
  have hregion : ¬(2*(336*q+81)≤352*q+85) := by omega
  simp only [secNext,exactSection,if_neg h0,if_neg h1,
    if_neg hk0,if_neg hregion]
  have hka : 352*q+85-1=352*q+84 := by omega
  have hca : 2*(336*q+81)-(352*q+85)+3=320*q+80 := by omega
  rw [hka,hca]
  exact bounce_target_terminal q

private theorem second_parent_outputs_target (q : Nat) :
    secNext (88*q+19,468*q+111) = some (384*q+96,320*q+79) := by
  have h0 : 88*q+19≠0 := by omega
  have h1 : 88*q+19≠1 := by omega
  have hk0 : 468*q+111≠0 := by omega
  have hregion : ¬(2*(468*q+111)≤88*q+19) := by omega
  simp only [secNext,exactSection,if_neg h0,if_neg h1,
    if_neg hk0,if_neg hregion]
  have hka : 88*q+19-1=88*q+18 := by omega
  have hca : 2*(468*q+111)-(88*q+19)+3=848*q+206 := by omega
  rw [hka,hca]
  exact bounce_target_twice q

/-- Exact two-family preimage equation for every affine target, not merely
    a necessary overapproximation, at all natural parameter values. -/
theorem target_section_inverse_iff (q a k : Nat) :
    secNext (a,k)=some (384*q+96,320*q+79) ↔
    (a=352*q+85 ∧ k=336*q+81) ∨
    (a=88*q+19 ∧ k=468*q+111) := by
  constructor
  · exact target_section_inverse q a k
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact first_parent_outputs_target q
    · exact second_parent_outputs_target q

#print axioms first_parent_outputs_target
#print axioms second_parent_outputs_target
#print axioms target_section_inverse_iff
end BB6.Agent46
