import FullForcedFilter
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- A two-dimensional source-exact all-time forbidden cone, independent of
    any halting equation. Three forced original-section predecessors lead
    from these residues to an impossible positive-time odd image. -/
theorem affine_three_cone_unreachable
    (x y time : Nat)
    (hx : x%8=5)
    (hxy : (2*x+y)%128=6) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (x,y) := by
  let a := x+y-2
  let b := (y-2)/2
  let c := (a+b-4)/2
  let d := (a+3*b-10)/4
  let e := (c+d-5)/2
  let f := (c+3*d-9)/4
  have hall :
    4≤y ∧ y%2=0 ∧ (x+y)%4=1 ∧
    a%2=1 ∧ b%2=1 ∧ 5≤b ∧ (a+b)%4=0 ∧ (a+b)%16≠0 ∧ 24≤a+b ∧
    c%2=0 ∧ d%2=1 ∧ 5≤d ∧ (c+d+1)%16=8 ∧ 23≤c+d ∧
    5≤f ∧ f%2=1 ∧ (e+f)%4=2 := by
    dsimp [a,b,c,d,e,f]
    omega
  rcases hall with
    ⟨hy4,hye,hs1,haodd,hbodd,hb5,hs2,hs16,hab24,
      hceven,hdodd,hd5,hs3,hcd23,hf5,hfodd,hs4⟩
  intro ht
  have hreach1 : ∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (a,b) :=
    (BB6.Agent15.blank_reach_iff_affine x y hy4 hye hs1).mp
      ⟨time, ht⟩
  obtain ⟨n1,hn1⟩ := hreach1
  have hreach2 : ∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (c,d) :=
    (oddodd_lowval_blank_reach_iff a b haodd hbodd hb5 hs2 hs16 hab24).mp
      ⟨n1,by simpa [c,d] using hn1⟩
  obtain ⟨n2,hn2⟩ := hreach2
  have hreach3 : ∃ n, BB6.Agent8Section.run secNext n (some (5,1))=some (e,f) :=
    (odd_seven_blank_reach_iff c d hceven hdodd hd5 hs3 hcd23).mp
      ⟨n2,by simpa [e,f] using hn2⟩
  obtain ⟨n3,hn3⟩ := hreach3
  cases n3 with
  | zero =>
      have hs : (e,f)=(5,1) := by
        simpa [BB6.Agent8Section.run] using hn3.symm
      have hf1 : f=1 := congrArg Prod.snd hs
      omega
  | succ n =>
      have hi := blank_section_odd_image n e f hn3 hf5 hfodd
      omega

#print axioms affine_three_cone_unreachable
end BB6.Agent3
