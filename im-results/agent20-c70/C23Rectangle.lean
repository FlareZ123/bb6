import C70Root
import Lean.Elab.Tactic.Omega

namespace BB6.Agent20C23
open BB6.Agent46

/-- Infinite three-variable source invariant: every even-right section state
    of sum 23 mod 32 and right 4 mod 8 (at least twelve) is blank-absent.
    Exact predecessor inverse is exhausted in one section edge, and each
    possible predecessor contradicts the odd-right image theorem. -/
theorem blank_no_sum23_right4 (x y : Nat)
    (hy : 12≤y) (hy4 : y%8=4) (hs : (x+y)%32=23) :
    ¬ BB6.Agent3.CReach x y := by
  rintro ⟨time, ht⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at ht
      omega
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at ht
      | some p =>
          rcases p with ⟨a,k⟩
          have hedge : secNext (a,k)=some (x,y) := by
            simpa [BB6.Agent8Section.run,hp] using ht
          have hs16 : (x+y)%16=7 := by omega
          have hyEven : y%2=0 := by omega
          rcases BB6.Agent20C70.seven_inverse a k x y (by omega)
              hyEven hs16 hedge with ⟨ha,hy'⟩ | ⟨hsum,hcost⟩
          · have hk5 : 5≤k := by omega
            have hkOdd : k%2=1 := by omega
            have hbad : (a+k)%4=0 ∨ (a+k)%4=3 := by
              cases n with
              | zero => simp [BB6.Agent8Section.run] at hp; omega
              | succ m => exact BB6.Agent3.blank_section_odd_image m a k hp hk5 hkOdd
            omega
          · have hk5 : 5≤k := by omega
            have hkOdd : k%2=1 := by omega
            have hbad : (a+k)%4=0 ∨ (a+k)%4=3 := by
              cases n with
              | zero => simp [BB6.Agent8Section.run] at hp; omega
              | succ m => exact BB6.Agent3.blank_section_odd_image m a k hp hk5 hkOdd
            omega

#print axioms blank_no_sum23_right4
end BB6.Agent20C23
