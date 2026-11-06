import SectionAllInverse
import ValuationArithmetic
import Lean.Elab.Tactic.Omega

namespace BB6.Agent34Valuation
open BB6.Agent46

/-- All original high-input Machine C parents with even first counter
    have recursion depth at most the output-sum valuation minus two.
    The cost identity fixes depth parity from the output's first counter. -/
theorem even_parent_depth_parity (a k x y v u : Nat)
    (ha : 2 ≤ a) (hk : 0 < k) (hregion : a < 2*k) (heven : a%2=0)
    (hfact : x+y=2^v*(2*u+1))
    (hedge : secNext (a,k)=some (x,y)) :
    ∃ n : Nat, n+2 ≤ v ∧ (n+1)%2=x%2 := by
  have hi := (section_preimage_all_iff a k x y).mp hedge
  have ha0 : a≠0 := by omega
  have ha1 : a≠1 := by omega
  have hk0 : k≠0 := by omega
  have hlow : ¬2*k≤a := by omega
  simp only [sectionPreimageAll, if_neg ha0, if_neg ha1, if_neg hk0,
    if_neg hlow, if_pos heven] at hi
  obtain ⟨_,n,hsum,hcost⟩ := hi
  have hsum' : 2^n*(2*a+4)=2^v*(2*u+1) := by
    have hs : 2*(a-1)+6=2*a+4 := by omega
    rw [hs] at hsum
    exact hsum.symm.trans hfact
  have hcost' : 2*k+a+7+3*n=x+2*y := by omega
  exact ⟨n, even_input_depth_val a n v u heven hsum',
    even_input_depth_parity a k x y n heven hcost'⟩

/-- All original high-input Machine C parents with odd first counter and
    target right counter at least five satisfy the companion valuation
    and exact parity restrictions, through every recursive bounce depth. -/
theorem odd_parent_depth_parity (a k x y v u : Nat)
    (ha : 3 ≤ a) (hk : 0 < k) (hregion : a < 2*k) (hodd : a%2=1)
    (hy : 5 ≤ y) (hfact : x+y+1=2^v*(2*u+1))
    (hedge : secNext (a,k)=some (x,y)) :
    ∃ n : Nat, n+2 ≤ v ∧ n%2=x%2 := by
  have hi := (section_preimage_all_iff a k x y).mp hedge
  have ha0 : a≠0 := by omega
  have ha1 : a≠1 := by omega
  have hk0 : k≠0 := by omega
  have hlow : ¬2*k≤a := by omega
  have heven : a%2≠0 := by omega
  simp only [sectionPreimageAll, if_neg ha0, if_neg ha1, if_neg hk0,
    if_neg hlow, if_neg heven] at hi
  rcases hi with h3 | ⟨_,n,hsum,hcost⟩
  · omega
  · have hsum' : 2^n*(2*a+6)=2^v*(2*u+1) := by
      have hs : 2*(a-1)+8=2*a+6 := by omega
      rw [hs] at hsum
      exact hsum.symm.trans hfact
    have hcost' : 2*k+a+7+3*n=x+2*y := by omega
    exact ⟨n, odd_input_depth_val a n v u hodd hsum',
      odd_input_depth_parity a k x y n hodd hcost'⟩

#print axioms even_parent_depth_parity
#print axioms odd_parent_depth_parity
end BB6.Agent34Valuation
