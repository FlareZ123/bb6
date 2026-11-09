import Low1875Source
import LowQ7
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace BB6.Agent21LowQ7

/-- Original blank return orbit excludes the deeper q=7 modulo16 low ray. -/
theorem blank_no_6995_low (time u : Nat) :
    BB6.Agent8Section.run BB6.Agent46.secNext time (some (5,1)) ≠
      some (1,8192*u+3587) := by
  rw [BB6.Agent21Low1875.runF_eq_source]
  exact LocalQ7.runF_no_q7 BB6.Agent46.secNext
    (fun a k x y hy h => BB6.Agent21Low1875.source_inverse_is_pred a k x y hy h)
    time u

/-- Infinite first-stopping index m=6995 modulo 8192 is forbidden. -/
theorem first_stop_m6995_mod8192 (time m k : Nat)
    (hm : m%8192=6995) (hstop : k+3*m+4=2^(2*m+3)) :
    BB6.Agent8Section.run BB6.Agent46.secNext time (some (5,1)) ≠
      some (1,k) := by
  have hmmin : 6995≤m := by omega
  have hpow : 8192 ∣ (2:Nat)^(2*m+3) := by
    change (2:Nat)^13 ∣ (2:Nat)^(2*m+3)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hsum : (k+3*m+4)%8192=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hpow
  have hkmod : k%8192=3587 := by omega
  have hk : k=8192*(k/8192)+3587 := by omega
  rw [hk]
  exact blank_no_6995_low time (k/8192)


/-- Every displayed algebraic source edge is a real original section edge. -/
theorem real_three_edges (u : Nat) :
    BB6.Agent46.secNext (5160*u+2248,5612*u+2445) =
      some (4256*u+1855,6064*u+2645) ∧
    BB6.Agent46.secNext (4256*u+1855,6064*u+2645) =
      some (640*u+278,7872*u+3437) ∧
    BB6.Agent46.secNext (640*u+278,7872*u+3437) =
      some (4096*u+1792,6144*u+2688) := by
  constructor
  · apply (BB6.Agent46.complete_section_inverse _ _ _ _ (by omega)).mpr
    change Local1875.Pred (5160*u+2248) (5612*u+2445)
      (4256*u+1855) (6064*u+2645)
    exact LocalQ7.q7_edge_E_Bp u
  constructor
  · apply (BB6.Agent46.complete_section_inverse _ _ _ _ (by omega)).mpr
    change Local1875.Pred (4256*u+1855) (6064*u+2645)
      (640*u+278) (7872*u+3437)
    exact LocalQ7.q7_edge_Bp_B u
  · apply (BB6.Agent46.complete_section_inverse _ _ _ _ (by omega)).mpr
    change Local1875.Pred (640*u+278) (7872*u+3437)
      (4096*u+1792) (6144*u+2688)
    exact LocalQ7.q7_edge_B_P u

private theorem source_edge_anc (p q : Nat × Nat)
    (h : BB6.Agent46.secNext p=some q) :
    Local1875.PredAll p.1 p.2 q.1 q.2 := by
  intro hy
  exact BB6.Agent21Low1875.source_inverse_is_pred p.1 p.2 q.1 q.2 hy
    (by simpa using h)

/-- Sharp arbitrary-start ancestry bound: the infinite P ray lies in the
    genuine three-step image and is disjoint from the four-step image. -/
theorem no_four_real_edges (u : Nat) (z0 z1 z2 z3 : Nat × Nat)
    (h01 : BB6.Agent46.secNext z0=some z1)
    (h12 : BB6.Agent46.secNext z1=some z2)
    (h23 : BB6.Agent46.secNext z2=some z3)
    (h3p : BB6.Agent46.secNext z3=some (4096*u+1792,6144*u+2688)) : False := by
  have h1 : LocalQ7.Anc 1 z1 :=
    LocalQ7.Anc.succ 0 z0.1 z0.2 z1.1 z1.2
      (by simpa using LocalQ7.Anc.zero z0) (source_edge_anc z0 z1 h01)
  have h2 : LocalQ7.Anc 2 z2 :=
    LocalQ7.Anc.succ 1 z1.1 z1.2 z2.1 z2.2 h1 (source_edge_anc z1 z2 h12)
  have h3 : LocalQ7.Anc 3 z3 :=
    LocalQ7.Anc.succ 2 z2.1 z2.2 z3.1 z3.2 h2 (source_edge_anc z2 z3 h23)
  have h4 : LocalQ7.Anc 4 (4096*u+1792,6144*u+2688) :=
    LocalQ7.Anc.succ 3 z3.1 z3.2 (4096*u+1792) (6144*u+2688) h3
      (source_edge_anc z3 (4096*u+1792,6144*u+2688) h3p)
  exact LocalQ7.no_p_anc_four u h4

#print axioms real_three_edges
#print axioms no_four_real_edges

#print axioms blank_no_6995_low
#print axioms first_stop_m6995_mod8192
end BB6.Agent21LowQ7
