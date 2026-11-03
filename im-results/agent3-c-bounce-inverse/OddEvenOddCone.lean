import FullForcedFilter
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- A second exact three-sector source-ancestry cone, with forced
    odd/odd, even/odd seven, odd/odd parents in that order.
    This independent source theorem has no halting-equation premise. -/
theorem odd_even_odd_cone_unreachable (x y time : Nat)
    (hx : x%8=3)
    (hxy : y%256=(x+94)%256)
    (hy9 : 9≤y) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (x,y) := by
  let a := (x+y-4)/2
  let b := (x+3*y-10)/4
  let c := (a+b-5)/2
  let d := (a+3*b-9)/4
  let e := (c+d-4)/2
  let f := (c+3*d-10)/4
  have hall :
    x%2=1 ∧ y%2=1 ∧ 5≤y ∧ (x+y)%4=0 ∧ (x+y)%16≠0 ∧ 24≤x+y ∧
    a%2=0 ∧ b%2=1 ∧ 5≤b ∧ (a+b+1)%16=8 ∧ 23≤a+b ∧
    c%2=1 ∧ d%2=1 ∧ 5≤d ∧ (c+d)%4=0 ∧ (c+d)%16≠0 ∧ 24≤c+d ∧
    5≤f ∧ f%2=1 ∧ (e+f)%4=1 := by
    dsimp [a,b,c,d,e,f]
    omega
  rcases hall with
    ⟨hxo,hyo,hy5,hs4,hs16,hs24,hae,hbo,hb5,hs7,hab23,
     hco,hdo,hd5,hcd4,hcd16,hcd24,hf5,hfo,hbad⟩
  intro ht
  have hreach1 : ∃ n, BB6.Agent8Section.run secNext n (some (5,1)) = some (a,b) :=
    (oddodd_lowval_blank_reach_iff x y hxo hyo hy5 hs4 hs16 hs24).mp
      ⟨time,ht⟩
  obtain ⟨n1,hn1⟩ := hreach1
  have hreach2 : ∃ n, BB6.Agent8Section.run secNext n (some (5,1)) = some (c,d) :=
    (odd_seven_blank_reach_iff a b hae hbo hb5 hs7 hab23).mp
      ⟨n1,by simpa [c,d] using hn1⟩
  obtain ⟨n2,hn2⟩ := hreach2
  have hreach3 : ∃ n, BB6.Agent8Section.run secNext n (some (5,1)) = some (e,f) :=
    (oddodd_lowval_blank_reach_iff c d hco hdo hd5 hcd4 hcd16 hcd24).mp
      ⟨n2,by simpa [e,f] using hn2⟩
  obtain ⟨n3,hn3⟩ := hreach3
  cases n3 with
  | zero =>
      have hs : (e,f)=(5,1) := by
        simpa [BB6.Agent8Section.run] using hn3.symm
      have hf1 : f=1 := congrArg Prod.snd hs
      omega
  | succ n =>
      have hi := blank_section_odd_image n e f hn3 hf5 hfo
      omega

#print axioms odd_even_odd_cone_unreachable
end BB6.Agent3
