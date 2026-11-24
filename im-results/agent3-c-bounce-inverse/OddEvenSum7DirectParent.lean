import SectionAllInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

private theorem n_add_two_le_two_pow (n : Nat) : n+2 ≤ 2^(n+1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      calc
        n+3 ≤ 2*(n+2) := by omega
        _ ≤ 2*2^(n+1) := Nat.mul_le_mul_left 2 ih
        _ = 2^(n+2) := by simp [pow_succ]

/-- In the complete source-preimage grammar, an odd/even target with
    sum+1 = 8 (mod 16) has no exceptional predecessor: only the direct
    section predecessor can occur. The odd-bounce branch is algebraically
    impossible after combining its two defining equations. -/
theorem sectionPreimageAll_odd_even_sum7_direct
    (a k x y : Nat)
    (hx : x%2=1) (hy : y%2=0) (hyge : 16≤y)
    (hplus16 : (x+y+1)%16=8)
    (hpre : sectionPreimageAll a k x y) :
    x=a-2*k ∧ y=2*k+2 := by
  by_cases ha0 : a=0
  · subst a
    by_cases hk0 : k=0
    · simp [sectionPreimageAll,hk0] at hpre
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,hk0,hk1] at hpre
        omega
      · have hk2 : 2≤k := by omega
        simp [sectionPreimageAll,hk0,hk1,hk2] at hpre
        rcases hpre with ⟨_,⟨n,hsum,_⟩⟩
        have hEven : (x+y)%2=0 := by
          rw [hsum]
          simp
        omega
  · by_cases ha1 : a=1
    · subst a
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,hk0] at hpre
        omega
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,hk0,hk1] at hpre
          omega
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,hk0,hk1,hk2] at hpre
            omega
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,hk0,hk1,hk2,hk3] at hpre
              omega
            · have hk4 : 4≤k := by omega
              simp [sectionPreimageAll,hk0,hk1,hk2,hk3,hk4] at hpre
              rcases hpre with hsmall|hlarge
              · rcases hsmall with ⟨hy3,_⟩
                omega
              · rcases hlarge with ⟨_,⟨n,hsum,_⟩⟩
                have hzero : (x+y+1)%16=0 := by rw [hsum]; simp
                omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at hpre
        omega
      · by_cases hdirect : 2*k≤a
        · simp [sectionPreimageAll,ha0,ha1,hk0,hdirect] at hpre
          rcases hpre with ⟨hx',hy'⟩
          omega
        · by_cases haEven : a%2=0
          · simp [sectionPreimageAll,ha0,ha1,hk0,hdirect,haEven] at hpre
            rcases hpre with ⟨_,⟨n,hsum,_⟩⟩
            have hEven : (x+y)%2=0 := by
              rw [hsum]
              simp
            omega
          · have haOdd : a%2=1 := by omega
            simp [sectionPreimageAll,ha0,ha1,hk0,hdirect,haEven] at hpre
            rcases hpre with hsmall|hlarge
            · rcases hsmall with ⟨hy3,_⟩
              omega
            · rcases hlarge with ⟨_,⟨n,hsum,hsecond⟩⟩
              have hyEq : y=2*k+2 := by omega
              have hxy : x+y=a+3*n+5 := by omega
              have hpow : n+2≤2^(n+1) := n_add_two_le_two_pow n
              have hbound : a+3*n+6 < (n+2)*(a+3) := by nlinarith
              have hmul : (n+2)*(a+3) ≤ 2^(n+1)*(a+3) :=
                Nat.mul_le_mul_right (a+3) hpow
              have hfirst : x+y+1=2^(n+1)*(a+3) := by
                calc
                  x+y+1 = 2^n*(2*(a-1)+8) := hsum
                  _ = 2^(n+1)*(a+3) := by
                    have hA : 2*(a-1)+8=2*(a+3) := by omega
                    rw [hA]
                    simp [pow_succ]
                    ring
              have hcontra : a+3*n+6 < 2^(n+1)*(a+3) :=
                lt_of_lt_of_le hbound hmul
              omega

end BB6.Agent46
