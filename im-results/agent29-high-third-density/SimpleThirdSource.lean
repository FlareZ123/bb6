import SimpleThirdArithmetic
import SectionAllInverse
import Agent3CImage
import GenericSection
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29Simple
open BB6.Agent46

/-- The local exact grammar is definitionally the original-source
    preimage predicate checked against the unchanged original secNext. -/
private theorem source_preimage (a k x y : Nat)
    (h : secNext (a,k)=some (x,y)) : P a k x y := by
  exact (section_preimage_all_iff a k x y).mp h

private theorem source_edge (a k x y : Nat)
    (h : P a k x y) : secNext (a,k)=some (x,y) := by
  exact (section_preimage_all_iff a k x y).mpr h

/-- The entire odd-right strip lies in the authentic two-step image. -/
theorem two_edges (x y : Nat)
    (hx : 7≤x) (hy : 512≤y)
    (hs : (x+y)%32=8 ∧ y%16=9 ∨
          (x+y)%32=24 ∧ y%16=1) :
    ∃ a k b l,
      secNext (b,l)=some (a,k) ∧ secNext (a,k)=some (x,y) := by
  obtain ⟨a,k,h1,ha,hk,heven⟩ := first_exists x y hx hy hs
  obtain ⟨b,l,h2⟩ := second_exists a k ha hk heven
  exact ⟨a,k,b,l,source_edge b l a k h2,source_edge a k x y h1⟩

/-- Every purported third original-source predecessor would have to
    output a prohibited odd-right (sum=1 mod 4) section state. -/
theorem no_three_edges (u v b l a k x y : Nat)
    (hx : 7≤x) (hy : 512≤y)
    (hs : (x+y)%32=8 ∧ y%16=9 ∨
          (x+y)%32=24 ∧ y%16=1)
    (hthird : secNext (u,v)=some (b,l))
    (hsecond : secNext (b,l)=some (a,k))
    (hfirst : secNext (a,k)=some (x,y)) : False := by
  have hmod16 : (x+y)%16=8 := by omega
  have hyodd : y%2=1 := by omega
  obtain ⟨haeq,hkeq⟩ := only_first a k x y hx hy hmod16 hyodd
    (source_preimage a k x y hfirst)
  obtain ⟨ha4,hk8,hsum⟩ := first_parent_residues a k x y hs haeq hkeq
  have ha128 : 128≤a := by omega
  have hk128 : 128≤k := by omega
  obtain ⟨hl5,hlodd,hbad⟩ := second_terminal b l a k
    ha128 hk128 ha4 hk8 hsum (source_preimage b l a k hsecond)
  have himage := BB6.Agent3.section_odd_image u v b l hthird hl5 hlodd
  omega

/-- No third incoming chain from any source, without a time bound. -/
theorem all_source_no_three (start : Nat×Nat) (n x y : Nat)
    (hx : 7≤x) (hy : 512≤y)
    (hs : (x+y)%32=8 ∧ y%16=9 ∨
          (x+y)%32=24 ∧ y%16=1) :
    BB6.Agent8Section.run secNext (n+3) (some start) ≠ some (x,y) := by
  intro ht
  have htime : n+3=((n+1)+1)+1 := by omega
  rw [htime] at ht
  change (BB6.Agent8Section.run secNext ((n+1)+1) (some start)).bind secNext =
    some (x,y) at ht
  cases hp : BB6.Agent8Section.run secNext ((n+1)+1) (some start) with
  | none => simp [hp] at ht
  | some p =>
      rcases p with ⟨a,k⟩
      have hfirst : secNext (a,k)=some (x,y) := by simpa [hp] using ht
      change (BB6.Agent8Section.run secNext (n+1) (some start)).bind secNext =
        some (a,k) at hp
      cases hq : BB6.Agent8Section.run secNext (n+1) (some start) with
      | none => simp [hq] at hp
      | some q =>
          rcases q with ⟨b,l⟩
          have hsecond : secNext (b,l)=some (a,k) := by simpa [hq] using hp
          change (BB6.Agent8Section.run secNext n (some start)).bind secNext =
            some (b,l) at hq
          cases h0 : BB6.Agent8Section.run secNext n (some start) with
          | none => simp [h0] at hq
          | some p =>
              rcases p with ⟨u,v⟩
              have hthird : secNext (u,v)=some (b,l) := by simpa [h0] using hq
              exact no_three_edges u v b l a k x y hx hy hs
                hthird hsecond hfirst

/-- Every target in the strip is absent from the genuine blank section
    orbit, including the first three exceptional section times. -/
theorem blank_unreachable (time x y : Nat)
    (hx : 7≤x) (hy : 512≤y)
    (hs : (x+y)%32=8 ∧ y%16=9 ∨
          (x+y)%32=24 ∧ y%16=1) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (x,y) := by
  cases time with
  | zero =>
      intro h
      simp [BB6.Agent8Section.run] at h
      omega
  | succ n =>
      cases n with
      | zero =>
          intro h
          have hfirst : secNext (5,1)=some (3,4) := by decide
          simp [BB6.Agent8Section.run,hfirst] at h
          omega
      | succ n =>
          cases n with
          | zero =>
              intro h
              have hfirst : secNext (5,1)=some (3,4) := by decide
              have hsecond : secNext (3,4)=some (4,7) := by
                simp [secNext,exactSection,bounce]
              simp [BB6.Agent8Section.run,hfirst,hsecond] at h
              omega
          | succ n =>
              simpa only [show n+1+1+1=n+3 by omega] using
                all_source_no_three (5,1) n x y hx hy hs

/-- Infinite 1/128-density high-stopping parameter lattice excluded
    from the true blank-start Machine C section orbit at every time. -/
theorem high_stop_blank_unreachable (j m k time : Nat)
    (hm : 4≤m) (hm4 : m%4=0) (hj : (j+m)%32=26)
    (hgate : k+j+3*m+5=(2:Nat)^(2*m+2)*(j+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*j+3,k) := by
  obtain ⟨hx,hy⟩ := high_stop_bounds j m k hm hm4 hj hgate
  have hs := high_stop_strip j m k hm hm4 hj hgate
  exact blank_unreachable time (2*j+3) k hx hy hs

#print axioms two_edges
#print axioms no_three_edges
#print axioms blank_unreachable
#print axioms high_stop_blank_unreachable
end BB6.Agent29Simple
