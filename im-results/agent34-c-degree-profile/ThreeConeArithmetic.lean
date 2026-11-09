import ConeBroadArithmetic
import Lean.Elab.Tactic.Omega

namespace BB6.Agent34Three
open BB6.Agent34Broad (sectionPreimageAll)

private theorem odd_high_impossible (a k x y n : Nat)
    (ha : 3 ≤ a) (hregion : a<2*k) (haodd : a%2=1) (hy : y%2=0)
    (hsum : (x+y)%8=1 ∨ (x+y)%8=3)
    (hpow : x+y+1=2^n*(2*(a-1)+8))
    (hcost : (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2) : False := by
  by_cases hn : n=0
  · subst n
    simp at hpow hcost
    omega
  · have hn1 : 1≤n := by omega
    have hp : 2 ∣ (2:Nat)^n := by
      have hd : (2:Nat)^1 ∣ (2:Nat)^n := Nat.pow_dvd_pow 2 hn1
      simpa using hd
    obtain ⟨p,hp⟩ := hp
    have hd : 4 ∣ 2*(a-1)+8 := by
      refine ⟨(a-1)/2+2,?_⟩
      omega
    obtain ⟨q,hq⟩ := hd
    have h8 : 8∣x+y+1 := by
      refine ⟨p*q,?_⟩
      calc
        x+y+1=2^n*(2*(a-1)+8) := hpow
        _=(2*p)*(4*q) := by rw [hp,hq]
        _=(2*4)*(p*q) := by ac_rfl
        _=8*(p*q) := by simp
    have hmod : (x+y+1)%8=0 := Nat.mod_eq_zero_of_dvd h8
    omega

private theorem even_high_impossible (a x y n : Nat)
    (hsum : (x+y)%8=1 ∨ (x+y)%8=3)
    (hpow : x+y=2^n*(2*(a-1)+6)) : False := by
  have h2 : 2∣x+y := by
    refine ⟨2^n*((a-1)+3),?_⟩
    calc
      x+y=2^n*(2*(a-1)+6) := hpow
      _=2^n*(2*((a-1)+3)) := by
        congr 1
      _=2*(2^n*((a-1)+3)) := by ac_rfl
  have hmod : (x+y)%2=0 := Nat.mod_eq_zero_of_dvd h2
  omega

/-- Under these parity/valuation conditions, every exact source parent
is the direct low-input parent. -/
theorem only_direct (a k x y : Nat)
    (hy : 6≤y) (hye : y%2=0)
    (hsum : (x+y)%8=1 ∨ (x+y)%8=3)
    (h : sectionPreimageAll a k x y) :
    a=x+y-2 ∧ 2*k+2=y := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at h
        omega
      · simp only [sectionPreimageAll,if_pos ha0,if_neg hk0,if_neg hk1] at h
        obtain ⟨_,n,hs,_⟩ := h
        have hdiv : 8∣x+y := by
          refine ⟨2^n,?_⟩
          rw [hs]
          ac_rfl
        have hzero : (x+y)%8=0 := Nat.mod_eq_zero_of_dvd hdiv
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at h
        omega
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,ha0,ha1,hk0,hk1] at h
          omega
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at h
            omega
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at h
              omega
            · simp only [sectionPreimageAll,if_neg ha0,if_pos ha1,
                if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at h
              rcases h with ⟨h3,_⟩ | ⟨_,n,hs,_⟩
              · omega
              · have hd : 8 ∣ x+y+1 := by
                  refine ⟨2^n*2,?_⟩
                  calc
                    x+y+1=2^n*16 := hs
                    _=8*(2^n*2) := by omega
                have hh : (x+y+1)%8=0 := Nat.mod_eq_zero_of_dvd hd
                omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at h
        omega
      · by_cases hlow : 2*k≤a
        · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,if_neg hk0,if_pos hlow] at h
          obtain ⟨hx,hy2⟩ := h
          constructor <;> omega
        · by_cases heven : a%2=0
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hlow,if_pos heven] at h
            obtain ⟨_,n,hs,_⟩ := h
            exact False.elim (even_high_impossible a x y n hsum hs)
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hlow,if_neg heven] at h
            rcases h with ⟨h3,_,_,_⟩ | ⟨_,n,hs,hc⟩
            · omega
            · have ha3 : 3≤a := by omega
              have haodd : a%2=1 := by omega
              exact False.elim (odd_high_impossible a k x y n ha3 (by omega) haodd hye hsum hs hc)

/-- Two forced direct reverse transitions expose a parent with odd
right coordinate and forbidden sum residue two. -/
theorem two_forced (a k b l x y : Nat)
    (hy : 34≤y)
    (hsector : ((x+y)%8=1 ∧ y%16=10) ∨
               ((x+y)%8=3 ∧ y%16=2))
    (hedge1 : sectionPreimageAll a k x y)
    (hedge2 : sectionPreimageAll b l a k) :
    5≤l ∧ l%2=1 ∧ (b+l)%4=2 := by
  have heven : y%2=0 := by omega
  have hsum : (x+y)%8=1 ∨ (x+y)%8=3 := by omega
  obtain ⟨ha,hk⟩ := only_direct a k x y (by omega) heven hsum hedge1
  have hkeven : k%2=0 := by omega
  have hkmin : 6≤k := by omega
  have hsum2 : (a+k)%8=1 ∨ (a+k)%8=3 := by omega
  obtain ⟨hb,hl⟩ := only_direct b l a k hkmin hkeven hsum2 hedge2
  omega

#print axioms only_direct
#print axioms two_forced
end BB6.Agent34Three
