import WordBlock
import FullSectionInverse

namespace BB6.Agent12WordBlock
open BB6.Agent46

theorem source_edge_law : EdgeLaw secNext := by
  intro a k x y r hr ha hk hy hb hm hA
  apply (complete_section_inverse a k x y (by omega)).2
  simp only [sectionPreimageCriterion,show a≠0 by omega,show a≠1 by omega,show k≠0 by omega,ite_false]
  by_cases h : r=1
  · rw [if_pos h] at hb
    simp only [hb,ite_true]
    rw [h] at hm hA
    simp at hA
    omega
  · rw [if_neg h] at hb
    simp only [show ¬2*k≤a by omega,ite_false]
    let n := r-2
    have hrn : r=n+2 := by dsimp [n]; omega
    have hp : 2^r=4*2^n := by rw [hrn,Nat.pow_add]; simp; ac_rfl
    rw [hp] at hA
    by_cases ho : a%2=0
    · simp only [ho,ite_true]
      refine ⟨n,?_,?_⟩
      · rw [ho] at hA
        have hmul : 4*2^n*(a+2+0)=2*(2^n*(2*(a-1)+6)) := by
          rw [show 2*(a-1)+6=2*(a+2) by omega,Nat.add_zero,show (4:Nat)=2*2 by decide]; ac_rfl
        rw [hmul] at hA
        omega
      · dsimp [n]; omega
    · have ho1 : a%2=1 := by omega
      simp only [ho,ite_false]
      refine ⟨n,?_,?_⟩
      · rw [ho1] at hA
        have hmul : 4*2^n*(a+2+1)=2*(2^n*(2*(a-1)+8)) := by
          rw [show 2*(a-1)+8=2*(a+2+1) by omega,show (4:Nat)=2*2 by decide]; ac_rfl
        rw [hmul] at hA
        omega
      · dsimp [n]; omega

theorem source_block (rs : List Nat) (s t : State)
    (hr : ∀ r ∈ rs, 1≤r) (hm : 8*2^shift rs≤s.m) (hp : consistent s)
    (he : applyCoeff (coeff rs (s.m%2)) s=t)
    (hx : 0≤t.a) (hg : 20*(2:Int)^shift rs≤gap t+4) :
    runNext secNext rs.length (some (decode s))=some (decode t) :=
  block_certificate secNext source_edge_law rs s t hr hm hp he hx hg

#print axioms source_edge_law
#print axioms source_block
end BB6.Agent12WordBlock
