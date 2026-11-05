import EvenChild
import OddSliver
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- The B rectangle has no incoming path of length three from any root.
    Its two predecessors are forced; the second predecessor has odd right
    counter and forbidden total mass modulo four. -/
theorem child_B_no_three_edges (p q a k u v r s : Nat)
    (h1 : secNext (a,k)=some (16*p+11,32*q+32))
    (h2 : secNext (u,v)=some (a,k))
    (h3 : secNext (r,s)=some (u,v)) : False := by
  obtain ⟨ha,hk⟩ := (even_child_parent_iff a k (16*p+11) (32*q+32)
    (by omega) (by omega) (by omega) (by omega)).mp h1
  have hu := odd_sliver_parents_forbidden u v a k
    (by omega) (by omega) (by omega) (by omega) (by omega) h2
  have hi := section_odd_image r s u v h3 (by omega) (by omega)
  omega

/-- Every orbit, regardless of its initial section state, avoids the entire
    B rectangle at times three and greater. This is an all-start theorem. -/
theorem child_B_no_three (start : Nat × Nat) (time p q : Nat) :
    BB6.Agent8Section.run secNext (time+3) (some start) ≠
      some (16*p+11,32*q+32) := by
  intro hh
  rw [show time+3=(time+2)+1 by omega] at hh
  change (BB6.Agent8Section.run secNext (time+2) (some start)).bind secNext =
    some (16*p+11,32*q+32) at hh
  cases h2 : BB6.Agent8Section.run secNext (time+2) (some start) with
  | none => simp [h2] at hh
  | some z =>
      rcases z with ⟨a,k⟩
      have hs1 : secNext (a,k)=some (16*p+11,32*q+32) := by
        simpa [h2] using hh
      rw [show time+2=(time+1)+1 by omega] at h2
      change (BB6.Agent8Section.run secNext (time+1) (some start)).bind secNext =
        some (a,k) at h2
      cases h1 : BB6.Agent8Section.run secNext (time+1) (some start) with
      | none => simp [h1] at h2
      | some z =>
          rcases z with ⟨u,v⟩
          have hs2 : secNext (u,v)=some (a,k) := by simpa [h1] using h2
          change (BB6.Agent8Section.run secNext time (some start)).bind secNext =
            some (u,v) at h1
          cases h0 : BB6.Agent8Section.run secNext time (some start) with
          | none => simp [h0] at h1
          | some z =>
              rcases z with ⟨r,s⟩
              have hs3 : secNext (r,s)=some (u,v) := by simpa [h0] using h1
              exact child_B_no_three_edges p q a k u v r s hs1 hs2 hs3

/-- The second predecessor edge is an ordinary one-branch odd bounce,
    with no recursion-depth cutoff. -/
private theorem B_parent_first (p q : Nat) :
    secNext (8*p+24*q+26,4*p+20*q+19)=some (16*p+32*q+41,16*q+15) := by
  have h0 : 8*p+24*q+26≠0 := by omega
  have h1 : 8*p+24*q+26≠1 := by omega
  have hk0 : 4*p+20*q+19≠0 := by omega
  have hl : ¬(2*(4*p+20*q+19)≤8*p+24*q+26) := by omega
  have ha : 8*p+24*q+26-1=8*p+24*q+25 := by omega
  have hc : 2*(4*p+20*q+19)-(8*p+24*q+26)+3=16*q+15 := by omega
  have hcl : ¬(16*q+15<4) := by omega
  have hodd : (8*p+24*q+25)%2=1 := by omega
  have hchi : 16*q+15≤2*(8*p+24*q+25)+6 := by omega
  unfold secNext exactSection
  simp only [if_neg h0,if_neg h1,if_neg hk0,if_neg hl]
  rw [ha,hc]
  rw [bounce]
  simp only [if_neg hcl,if_pos hodd,if_pos hchi]
  congr 1
  congr 1
  omega

private theorem B_parent_second (p q : Nat) :
    secNext (16*p+32*q+41,16*q+15)=some (16*p+11,32*q+32) := by
  apply (even_child_parent_iff _ _ _ _
    (by omega) (by omega) (by omega) (by omega)).mpr
  constructor <;> omega

/-- Sharpness: two real source section edges reach every B rectangle point
    from a suitable nonblank initial section state. -/
theorem child_B_two_witness (p q : Nat) :
    BB6.Agent8Section.run secNext 2
      (some (8*p+24*q+26,4*p+20*q+19)) =
    some (16*p+11,32*q+32) := by
  simp [BB6.Agent8Section.run,B_parent_first,B_parent_second]

#print axioms child_B_no_three
#print axioms child_B_two_witness
end BB6.Agent3
