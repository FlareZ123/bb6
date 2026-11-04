import OddOddOrbit
import Agent3CImage
import SectionParam
import Lean.Elab.Tactic.Omega

namespace BB6.Agent1Unified
open BB6.Agent46

/-- Two-level exclusion: the exact predecessor of any odd-odd
    valuation-two image lies in the globally empty even/odd
    output residue (0,1) mod 4. -/
theorem oddodd_zeroone_parent_unreachable (x y time : Nat)
    (hx : x%2=1) (hy : y%2=1) (hy5 : 5≤y)
    (hs : (x+y)%8=4)
    (ha : ((x+y-4)/2)%4=0)
    (hk : ((x+3*y-10)/4)%4=1)
    (hk5 : 5≤((x+3*y-10)/4)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (x,y) := by
  intro hr
  obtain ⟨n,hn⟩ := (BB6.Agent3.oddodd_blank_reach_iff x y hx hy hy5 hs).mp
    ⟨time,hr⟩
  let a : Nat := (x+y-4)/2
  let k : Nat := (x+3*y-10)/4
  change BB6.Agent8Section.run secNext n (some (5,1)) = some (a,k) at hn
  cases n with
  | zero =>
      simp [BB6.Agent8Section.run] at hn
      have hfirst : a%4=0 := ha
      dsimp [a] at hfirst
      omega
  | succ n =>
      have hy' : 5≤k := hk5
      have ho' : k%2=1 := by omega
      have hv := BB6.Agent3.blank_section_odd_image n a k hn hy' ho'
      have ha' : a%4=0 := ha
      have hk' : k%4=1 := hk
      omega

/-- Infinitely many complete m=0 high-stopping gates (u≡3 mod16)
    are absent from the authentic Machine C blank section. -/
theorem high_depth_zero_3mod16_unreachable (time t : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (32*t+7,48*t+13) := by
  apply oddodd_zeroone_parent_unreachable
  all_goals omega

/-- Each excluded high-depth-zero point really is an immediate
    stopping input, an all-time exclusion of actual candidate gates. -/
theorem high_depth_zero_3mod16_is_gate (t : Nat) :
    secNext (32*t+7,48*t+13) = none := by
  apply (BB6.Agent15.section_halts_iff_parametric (32*t+7) (48*t+13)).mpr
  right
  right
  refine ⟨16*t+2,0,by omega,?_⟩
  norm_num
  omega

#print axioms oddodd_zeroone_parent_unreachable
#print axioms high_depth_zero_3mod16_unreachable
#print axioms high_depth_zero_3mod16_is_gate
end BB6.Agent1Unified
