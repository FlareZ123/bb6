import OddEvenVal2
import OddOddZeroOne
import SectionAffineInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent1Unified
open BB6.Agent46

/-- Exact backwards implication for the authentic blank orbit,
    using the new odd/even valuation-two predecessor uniqueness. -/
private theorem blank_reaches_odd_even_direct_parent (x y : Nat)
    (hx : x%2=1) (hy : y%2=0) (hy4 : 4≤y)
    (hs : (x+y+1)%8=4)
    (h : ∃ t, BB6.Agent8Section.run secNext t (some (5,1))=some (x,y)) :
    ∃ t, BB6.Agent8Section.run secNext t (some (5,1)) =
      some (x+y-2,(y-2)/2) := by
  obtain ⟨time,ht⟩ := h
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at ht
      omega
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at ht
      | some pair =>
          rcases pair with ⟨a,k⟩
          have he : secNext (a,k)=some (x,y) := by
            simpa [BB6.Agent8Section.run,hp] using ht
          obtain ⟨ha,hk⟩ := odd_even_val2_forces_direct a k x y hx hy hy4 hs he
          have hk' : k=(y-2)/2 := by omega
          refine ⟨n,?_⟩
          simpa [ha,hk'] using hp

/-- The older Agent15 exact affine inverse handles the third forced step
    when its target has even right counter and sum 1 mod 4. -/
private theorem blank_reaches_sumone_direct_parent (x y : Nat)
    (hy4 : 4≤y) (hy : y%2=0) (hs : (x+y)%4=1)
    (h : ∃ t, BB6.Agent8Section.run secNext t (some (5,1))=some (x,y)) :
    ∃ t, BB6.Agent8Section.run secNext t (some (5,1)) =
      some (x+y-2,(y-2)/2) := by
  obtain ⟨time,ht⟩ := h
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at ht
      omega
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at ht
      | some pair =>
          rcases pair with ⟨a,k⟩
          have he : secNext (a,k)=some (x,y) := by
            simpa [BB6.Agent8Section.run,hp] using ht
          obtain ⟨ha,hk⟩ := (BB6.Agent15.section_sum_one_even_iff_affine
            a k x y hy4 hy hs).mp he
          refine ⟨n,?_⟩
          simpa [ha,hk] using hp

/-- A complete infinite high stopping class missed by Agent43's B8/M32
    reachable-state quotient: depth m=0, odd parameter j=128*p+5, p≥1.
    Three forced direct inverse steps end in the source-certified
    odd-odd zero-one forbidden cone. -/
theorem high_depth_zero_6mod128_unreachable (p time : Nat) (hp : 1≤p) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (256*p+13,384*p+22) := by
  intro htarget
  obtain ⟨t1,h1⟩ := blank_reaches_odd_even_direct_parent
    (256*p+13) (384*p+22) (by omega) (by omega) (by omega)
    (by omega) ⟨time,htarget⟩
  have ha1 : (256*p+13)+(384*p+22)-2=640*p+33 := by omega
  have hk1 : ((384*p+22)-2)/2=192*p+10 := by omega
  rw [ha1,hk1] at h1
  obtain ⟨t2,h2⟩ := blank_reaches_odd_even_direct_parent
    (640*p+33) (192*p+10) (by omega) (by omega) (by omega)
    (by omega) ⟨t1,h1⟩
  have ha2 : (640*p+33)+(192*p+10)-2=832*p+41 := by omega
  have hk2 : ((192*p+10)-2)/2=96*p+4 := by omega
  rw [ha2,hk2] at h2
  obtain ⟨t3,h3⟩ := blank_reaches_sumone_direct_parent
    (832*p+41) (96*p+4) (by omega) (by omega) (by omega)
    ⟨t2,h2⟩
  have ha3 : (832*p+41)+(96*p+4)-2=928*p+43 := by omega
  have hk3 : ((96*p+4)-2)/2=48*p+1 := by omega
  rw [ha3,hk3] at h3
  have hforbid := oddodd_zeroone_parent_unreachable
    (928*p+43) (48*p+1) t3 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  exact hforbid h3

/-- These genuine high-family depth-zero stopping candidates satisfy
    the unchanged, complete source classification. -/
theorem high_depth_zero_6mod128_are_gates (p : Nat) :
    secNext (256*p+13,384*p+22)=none := by
  apply (BB6.Agent15.section_halts_iff_parametric
    (256*p+13) (384*p+22)).mpr
  right
  right
  refine ⟨128*p+5,0,by omega,?_⟩
  simp only [show (2:Nat)^(2*0+2)=4 by decide]
  omega

#print axioms high_depth_zero_6mod128_unreachable
#print axioms high_depth_zero_6mod128_are_gates
end BB6.Agent1Unified
