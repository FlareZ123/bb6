import SectionAllInverse
import UnboundedInDegree
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Base-two powers are injective in the natural-number exponent. -/
theorem degree_pow2_inj (n m : Nat) (h : 2^n = 2^m) : n=m := by
  by_cases he : n=m
  · exact he
  · by_cases hlt : n<m
    · have hh:=Nat.pow_lt_pow_right (by decide : 1<2) hlt
      omega
    · have hgt:m<n := by omega
      have hh:=Nat.pow_lt_pow_right (by decide : 1<2) hgt
      omega

theorem degree_two_pow_double (r : Nat) : 2^(2*r)=4^r := by
  calc
    2^(2*r)=(2^2)^r := Nat.pow_mul 2 2 r
    _=4^r := by simp

theorem degree_odd_parent_depth (n t : Nat)
    (h : 2^n*8=16*4^t) : n=2*t+1 := by
  have hpow : 2^(n+3)=2^(2*t+4) := by
    calc
      2^(n+3)=2^n*2^3 := Nat.pow_add 2 n 3
      _=16*4^t := by simpa using h
      _=2^(2*t+4) := by
        rw [Nat.pow_add,degree_two_pow_double]
        omega
  have he := degree_pow2_inj (n+3) (2*t+4) hpow
  omega

theorem degree_high_even_depth_odd (a k n y : Nat)
    (ha : a%2=0) (hc : 2*k+a+7+3*n=2*y) : n%2=1 := by
  omega

/-- Product-power inversion at the precise exponential target. -/
theorem degree_high_parent_power (t n a : Nat)
    (ha : 2≤a) (h : 2^n*(2*a+4)=16*4^t) :
    n≤2*t+1 ∧ 2*a+4=2^(2*t+4-n) := by
  have h2 : 8≤2*a+4 := by omega
  have hle : 2^n*8≤16*4^t := by
    calc
      2^n*8 ≤ 2^n*(2*a+4) := Nat.mul_le_mul_left (2^n) h2
      _ = 16*4^t := h
  have hpow : 2^(n+3)≤2^(2*t+4) := by
    calc
      2^(n+3)=2^n*2^3 := Nat.pow_add 2 n 3
      _=2^n*8 := by rfl
      _≤16*4^t := hle
      _=2^(2*t+4) := by rw [Nat.pow_add,degree_two_pow_double]; omega
  have hn : n+3≤2*t+4 := by
    by_cases hh : n+3≤2*t+4
    · exact hh
    · have hgt : 2*t+4<n+3 := by omega
      have hstrict := Nat.pow_lt_pow_right (by decide : 1<2) hgt
      omega
  have hn' : n≤2*t+1 := by omega
  have hsplit : 2^(2*t+4)=2^n*2^(2*t+4-n) := by
    have he : n+(2*t+4-n)=2*t+4 := by omega
    calc
      2^(2*t+4)=2^(n+(2*t+4-n)) := by rw [he]
      _=2^n*2^(2*t+4-n) := Nat.pow_add 2 n (2*t+4-n)
  have hcalc : 2^n*(2*a+4)=2^n*2^(2*t+4-n) := by
    calc
      2^n*(2*a+4)=16*4^t := h
      _=2^(2*t+4) := by rw [Nat.pow_add,degree_two_pow_double]; omega
      _=2^n*2^(2*t+4-n) := hsplit
  exact ⟨hn',Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide : 0<2)) hcalc⟩

/-- Exhaust every original source branch for target (0,16*4^t).
    In particular, no additional odd-first high source or exceptional
    one-left source exists, at ANY bounce recursion depth. -/
theorem power_target_parents_only (t a k : Nat)
    (h : sectionPreimageAll a k 0 (16*4^t)) :
    (a=0 ∧ k=16*4^t-(3*t+6)) ∨
    (a=16*4^t-2 ∧ k=8*4^t-1) ∨
    (∃ r : Nat, r≤t ∧ a=4*4^(t-r)-2 ∧
      k=16*4^t-(2*4^(t-r)+3*r+4)) := by
  let Y : Nat := 16*4^t
  have hY : 16≤Y := by
    have hh:=Nat.one_le_pow t 4 (by decide)
    dsimp [Y]
    omega
  have hYeven : Y%2=0 := by dsimp [Y]; omega
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [sectionPreimageAll,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [sectionPreimageAll,ha0,hk0,hk1] at h
        omega
      · simp only [sectionPreimageAll,if_pos ha0,if_neg hk0,if_neg hk1] at h
        rcases h with ⟨_,n,hs,hc⟩
        have hn : n=2*t+1 := by
          apply degree_odd_parent_depth n t
          simpa using hs.symm
        left
        constructor
        · exact ha0
        · dsimp [Y] at *
          omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at h
      · by_cases hk1 : k=1
        · simp [sectionPreimageAll,ha0,ha1,hk0,hk1] at h
        · by_cases hk2 : k=2
          · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2] at h
          · by_cases hk3 : k=3
            · simp [sectionPreimageAll,ha0,ha1,hk0,hk1,hk2,hk3] at h
              omega
            · simp only [sectionPreimageAll,if_neg ha0,if_pos ha1,if_neg hk0,
                if_neg hk1,if_neg hk2,if_neg hk3] at h
              rcases h with ⟨hy,_⟩ | ⟨_,n,hs,_⟩
              · omega
              · have hcontra : 16*4^t+1=16*(2^n) := by
                  simpa [Nat.mul_comm] using hs
                omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [sectionPreimageAll,ha0,ha1,hk0] at h
        omega
      · by_cases hlow : 2*k≤a
        · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,if_neg hk0,if_pos hlow] at h
          rcases h with ⟨hx,hy⟩
          right
          left
          constructor
          · omega
          · omega
        · by_cases haEven : a%2=0
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,if_neg hk0,
              if_neg hlow,if_pos haEven] at h
            rcases h with ⟨_,n,hs,hc⟩
            have hcost : 2*k+a+7+3*n=2*(16*4^t) := by omega
            have hn : n%2=1 :=
              degree_high_even_depth_odd a k n (16*4^t) haEven hcost
            have hfactor : 2*(a-1)+6=2*a+4 := by omega
            have hsum : 2^n*(2*a+4)=16*4^t := by
              simpa only [hfactor,Nat.zero_add] using hs.symm
            obtain ⟨hdepth,hpower⟩ := degree_high_parent_power t n a ha2 hsum
            let r : Nat := n/2
            have hrn : n=2*r+1 := by dsimp [r]; omega
            have hrt : r≤t := by omega
            have heq : 2*a+4=8*4^(t-r) := by
              rw [show 2*t+4-n=2*(t-r)+3 by omega] at hpower
              rw [Nat.pow_add,degree_two_pow_double] at hpower
              omega
            have haeq : a=4*4^(t-r)-2 := by omega
            right
            right
            refine ⟨r,hrt,haeq,?_⟩
            omega
          · simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,if_neg hk0,
              if_neg hlow,if_neg haEven] at h
            rcases h with ⟨hy,_⟩ | ⟨_,n,hs,_⟩
            · omega
            · have hh : (16*4^t+1)%2=1 := by omega
              have hev : (2^n*(2*(a-1)+8))%2=0 := by
                have eq : 2*(a-1)+8 = 2*((a-1)+4) := by omega
                rw [eq]
                have hex : 2^n*(2*((a-1)+4))=2*(2^n*((a-1)+4)) := by ac_rfl
                rw [hex]
                omega
              omega

/-- The a=0 power-target predecessor is always a genuine arithmetic edge. -/
theorem zero_source_criterion (t : Nat) :
    sectionPreimageAll 0 (16*4^t-(3*t+6)) 0 (16*4^t) := by
  let Y : Nat := 16*4^t
  let k : Nat := Y-(3*t+6)
  have ht : t+1≤4^t := parent_four_ge t
  have hk : k+(3*t+6)=Y := by dsimp [k,Y]; omega
  have hk2 : 2≤k := by omega
  have hpow : 0+Y = 2^(2*t+1)*8 := by
    rw [Nat.pow_add,degree_two_pow_double]
    dsimp [Y]
    omega
  have hcost : (2*k+1)+8+3*(2*t+1)=0+2*Y := by omega
  have hk0 : k≠0 := by omega
  have hk1 : k≠1 := by omega
  change sectionPreimageAll 0 k 0 Y
  simp only [sectionPreimageAll,if_pos rfl,if_neg hk0,if_neg hk1]
  exact ⟨by omega,⟨2*t+1,hpow,hcost⟩⟩

/-- The direct low-branch predecessor is always a genuine arithmetic edge. -/
theorem direct_source_criterion (t : Nat) :
    sectionPreimageAll (16*4^t-2) (8*4^t-1) 0 (16*4^t) := by
  let P : Nat := 4^t
  let a : Nat := 16*P-2
  let k : Nat := 8*P-1
  have hp : 1≤P := Nat.one_le_pow t 4 (by decide)
  have hA : a+2=16*P := by dsimp [a]; omega
  have hK : k+1=8*P := by dsimp [k]; omega
  have ha0 : a≠0 := by omega
  have ha1 : a≠1 := by omega
  have hk0 : k≠0 := by omega
  have hlow : 2*k≤a := by omega
  have hx : a-2*k=0 := by omega
  have hy : 2*k+2=16*P := by omega
  change sectionPreimageAll a k 0 (16*P)
  simp only [sectionPreimageAll,if_neg ha0,if_neg ha1,if_neg hk0,if_pos hlow]
  exact ⟨hx.symm,hy.symm⟩

/-- Exact universally quantified classification, with EVERY arithmetic
    parent generating a real original section edge. For target (0,16*4^t)
    the first alternative is the a=0 exceptional sector, the second is the
    unique direct source, and the third consists of exactly t+1 distinct
    high even-a odd-bounce sources certified by family_parent. -/
theorem power_target_preimages_iff (t a k : Nat) :
    secNext (a,k)=some (0,16*4^t) ↔
    (a=0 ∧ k=16*4^t-(3*t+6)) ∨
    (a=16*4^t-2 ∧ k=8*4^t-1) ∨
    (∃ r : Nat, r≤t ∧ a=4*4^(t-r)-2 ∧
      k=16*4^t-(2*4^(t-r)+3*r+4)) := by
  constructor
  · intro h
    exact power_target_parents_only t a k
      ((section_preimage_all_iff a k 0 (16*4^t)).mp h)
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨r,hr,rfl,rfl⟩)
    · exact (section_preimage_all_iff 0 (16*4^t-(3*t+6)) 0 (16*4^t)).mpr
        (zero_source_criterion t)
    · exact (section_preimage_all_iff (16*4^t-2) (8*4^t-1) 0 (16*4^t)).mpr
        (direct_source_criterion t)
    · have he : t-(t-r)=r := by omega
      simpa only [he] using family_parent t (t-r) (by omega)

#print axioms power_target_preimages_iff
#print axioms power_target_parents_only
end BB6.Agent3
