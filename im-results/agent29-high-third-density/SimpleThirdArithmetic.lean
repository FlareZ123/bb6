import Lean
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace BB6.Agent29Simple

def P (a k x y : Nat) : Prop :=
  if a=0 then
    if k=0 then False
    else if k=1 then x=0 ∧ y=4
    else 4≤y ∧ ∃ n:Nat,
      x+y=2^n*8 ∧ (2*k+1)+8+3*n=x+2*y
  else if a=1 then
    if k=0 then x=5 ∧ y=1
    else if k=1 then x=2 ∧ y=3
    else if k=2 then x=2 ∧ y=5
    else if k=3 then x=0 ∧ y=7
    else
      (y=3 ∧ ∃ n:Nat, x+6=2^n*16 ∧
        (2*k-3)+16+3*n=x+10) ∨
      (5≤y ∧ ∃ n:Nat, x+y+1=2^n*16 ∧
        (2*k-3)+16+3*n=x+2*y+2)
  else if k=0 then x=a-2 ∧ y=2
  else if 2*k≤a then x=a-2*k ∧ y=2*k+2
  else if a%2=0 then
    4≤y ∧ ∃ n:Nat,
      x+y=2^n*(2*(a-1)+6) ∧
      (2*k-a+3)+(2*(a-1)+6)+3*n=x+2*y
  else
    (y=3 ∧ ∃ n:Nat, x+6=2^n*(2*(a-1)+8) ∧
      (2*k-a+3)+(2*(a-1)+8)+3*n=x+10) ∨
    (5≤y ∧ ∃ n:Nat, x+y+1=2^n*(2*(a-1)+8) ∧
      (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2)

private theorem even_factor_div4 (a : Nat) (ha : 2≤a) (he : a%2=0) :
  4 ∣ 2*(a-1)+6 := by
  apply Nat.dvd_of_mod_eq_zero
  omega

private theorem pow_even_div16 (a n s : Nat)
    (ha : 2≤a) (he : a%2=0) (hn : 2≤n)
    (hs : s=2^n*(2*(a-1)+6)) : s%16=0 := by
  have hd : 4 ∣ (2:Nat)^n := by
    have h := Nat.pow_dvd_pow 2 hn
    simpa using h
  obtain ⟨p,hp⟩ := hd
  obtain ⟨q,hq⟩ := even_factor_div4 a ha he
  have hp16 : 16 ∣ s := by
    refine ⟨p*q,?_⟩
    calc
      s=2^n*(2*(a-1)+6) := hs
      _=(4*p)*(4*q) := by rw [hp,hq]
      _=16*(p*q) := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  exact Nat.mod_eq_zero_of_dvd hp16

private theorem pow_zero_div16 (n s : Nat)
    (hn : 1≤n) (hs : s=2^n*8) : s%16=0 := by
  have hd : 2 ∣ (2:Nat)^n := by
    have h := Nat.pow_dvd_pow 2 hn
    simpa using h
  obtain ⟨p,hp⟩ := hd
  have hp16 : 16 ∣ s := by
    refine ⟨p,?_⟩
    calc
      s=2^n*8 := hs
      _=(2*p)*8 := by rw [hp]
      _=16*p := by omega
  exact Nat.mod_eq_zero_of_dvd hp16

/-- In the new congruence strip, every incoming original-formula edge
    is the unique depth-zero even-source bounce. -/
theorem only_first (a k x y : Nat)
    (hx : 7≤x) (hy : 512≤y) (hs : (x+y)%16=8)
    (hyodd : y%2=1) (h : P a k x y) :
    2*a+4=x+y ∧ 2*k+a+7=x+2*y := by
  have hxodd : x%2=1 := by omega
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [P,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [P,ha0,hk0,hk1] at h
        omega
      · simp only [P,if_pos ha0,if_neg hk0,if_neg hk1] at h
        obtain ⟨_,n,hpow,_⟩ := h
        by_cases hn : n=0
        · subst n; simp at hpow; omega
        · have hd := pow_zero_div16 n (x+y) (by omega) hpow
          omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [P,ha0,ha1,hk0] at h; omega
      · by_cases hk1 : k=1
        · simp [P,ha0,ha1,hk0,hk1] at h; omega
        · by_cases hk2 : k=2
          · simp [P,ha0,ha1,hk0,hk1,hk2] at h; omega
          · by_cases hk3 : k=3
            · simp [P,ha0,ha1,hk0,hk1,hk2,hk3] at h; omega
            · simp only [P,if_neg ha0,if_pos ha1,if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at h
              rcases h with ⟨he,_⟩ | ⟨_,n,hpow,_⟩
              · omega
              · have hd : 2∣x+y+1 := by
                  refine ⟨2^n*8,?_⟩
                  rw [hpow]
                  omega
                have hh := Nat.mod_eq_zero_of_dvd hd
                omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [P,ha0,ha1,hk0] at h; omega
      · by_cases hlow : 2*k≤a
        · simp [P,ha0,ha1,hk0,hlow] at h; omega
        · by_cases heven : a%2=0
          · simp only [P,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hlow,if_pos heven] at h
            obtain ⟨_,n,hpow,hcost⟩ := h
            have hn : n≤1 := by
              by_cases hn : n≤1
              · exact hn
              · have hd := pow_even_div16 a n (x+y) ha2 heven (by omega) hpow
                omega
            have hncase : n=0 ∨ n=1 := by omega
            rcases hncase with h0 | h1
            · subst n
              simp at hpow hcost
              omega
            · subst n
              simp at hpow hcost
              omega
          · simp only [P,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hlow,if_neg heven] at h
            rcases h with ⟨he,_⟩ | ⟨_,n,hpow,_⟩
            · omega
            · have hd : 2∣x+y+1 := by
                refine ⟨2^n*(a+3),?_⟩
                calc
                  x+y+1=2^n*(2*(a-1)+8) := hpow
                  _=2^n*(2*(a+3)) := by congr 1; omega
                  _=2*(2^n*(a+3)) := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
              have hh := Nat.mod_eq_zero_of_dvd hd
              omega

/-- The first predecessor has right coordinate 4 modulo 8 and
    coordinate sum 2 modulo 4, eliminating all bounce parents. -/
theorem first_parent_residues (a k x y : Nat)
    (hs : (x+y)%32=8 ∧ y%16=9 ∨
          (x+y)%32=24 ∧ y%16=1)
    (h1 : 2*a+4=x+y) (h2 : 2*k+a+7=x+2*y) :
    a%4=2 ∧ k%8=4 ∧ (a+k)%4=2 := by
  rcases hs with h | h <;> omega

/-- The unique possible second parent has odd right coordinate and
    sum 1 mod 4, violating the original odd-right image invariant. -/
theorem second_terminal (b l a k : Nat)
    (ha : 128≤a) (hk : 128≤k)
    (ha4 : a%4=2) (hk8 : k%8=4)
    (hsum : (a+k)%4=2) (h : P b l a k) :
    5≤l ∧ l%2=1 ∧ (b+l)%4=1 := by
  by_cases hb0 : b=0
  · by_cases hl0 : l=0
    · simp [P,hb0,hl0] at h
    · by_cases hl1 : l=1
      · simp [P,hb0,hl0,hl1] at h; omega
      · simp only [P,if_pos hb0,if_neg hl0,if_neg hl1] at h
        obtain ⟨_,n,hpow,_⟩ := h
        have hd : 4 ∣ a+k := by
          refine ⟨2^n*2,?_⟩
          rw [hpow]
          omega
        have hh := Nat.mod_eq_zero_of_dvd hd
        omega
  · by_cases hb1 : b=1
    · by_cases hl0 : l=0
      · simp [P,hb0,hb1,hl0] at h; omega
      · by_cases hl1 : l=1
        · simp [P,hb0,hb1,hl0,hl1] at h; omega
        · by_cases hl2 : l=2
          · simp [P,hb0,hb1,hl0,hl1,hl2] at h; omega
          · by_cases hl3 : l=3
            · simp [P,hb0,hb1,hl0,hl1,hl2,hl3] at h; omega
            · simp only [P,if_neg hb0,if_pos hb1,if_neg hl0,if_neg hl1,if_neg hl2,if_neg hl3] at h
              rcases h with ⟨he,_⟩ | ⟨_,n,hpow,_⟩
              · omega
              · have hd : 2 ∣ a+k+1 := by
                  refine ⟨2^n*8,?_⟩
                  rw [hpow]
                  omega
                have hh := Nat.mod_eq_zero_of_dvd hd
                omega
    · have hb2 : 2≤b := by omega
      by_cases hl0 : l=0
      · simp [P,hb0,hb1,hl0] at h; omega
      · by_cases hlow : 2*l≤b
        · simp [P,hb0,hb1,hl0,hlow] at h
          omega
        · by_cases heven : b%2=0
          · simp only [P,if_neg hb0,if_neg hb1,if_neg hl0,if_neg hlow,if_pos heven] at h
            obtain ⟨_,n,hpow,_⟩ := h
            have hd : 4 ∣ a+k := by
              obtain ⟨q,hq⟩ := even_factor_div4 b hb2 heven
              refine ⟨2^n*q,?_⟩
              rw [hpow,hq]
              simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
            have hh := Nat.mod_eq_zero_of_dvd hd
            omega
          · simp only [P,if_neg hb0,if_neg hb1,if_neg hl0,if_neg hlow,if_neg heven] at h
            rcases h with ⟨he,_⟩ | ⟨_,n,hpow,_⟩
            · omega
            · have hd : 2 ∣ a+k+1 := by
                refine ⟨2^n*(b+3),?_⟩
                calc
                  a+k+1=2^n*(2*(b-1)+8) := hpow
                  _=2^n*(2*(b+3)) := by congr 1; omega
                  _=2*(2^n*(b+3)) := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
              have hh := Nat.mod_eq_zero_of_dvd hd
              omega

/-- The unique depth-zero source has genuine source conditions. -/
theorem first_exists (x y : Nat)
    (hx : 7≤x) (hy : 512≤y)
    (hs : (x+y)%32=8 ∧ y%16=9 ∨
          (x+y)%32=24 ∧ y%16=1) :
    ∃ a k, P a k x y ∧ 128≤a ∧ 128≤k ∧ k%2=0 := by
  let a := (x+y-4)/2
  let k := (x+2*y-a-7)/2
  have haeq : 2*a+4=x+y := by dsimp [a]; omega
  have hkeq : 2*k+a+7=x+2*y := by dsimp [k]; omega
  have hres := first_parent_residues a k x y hs haeq hkeq
  obtain ⟨ha4,hk8,_⟩ := hres
  have ha128 : 128≤a := by omega
  have hk128 : 128≤k := by omega
  have ha0 : a≠0 := by omega
  have ha1 : a≠1 := by omega
  have hk0 : k≠0 := by omega
  have hhigh : ¬2*k≤a := by omega
  have heven : a%2=0 := by omega
  have hpre : P a k x y := by
    simp only [P,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hhigh,if_pos heven]
    constructor
    · omega
    · refine ⟨0,?_,?_⟩
      · simp; omega
      · simp; omega
  exact ⟨a,k,hpre,ha128,hk128,by omega⟩

/-- Every large even right target has an actual direct incoming edge. -/
theorem second_exists (a k : Nat) (ha : 128≤a) (hk : 128≤k)
    (heven : k%2=0) :
    ∃ b l, P b l a k := by
  let b := a+k-2
  let l := (k-2)/2
  have hb0 : b≠0 := by dsimp [b]; omega
  have hb1 : b≠1 := by dsimp [b]; omega
  have hl0 : l≠0 := by dsimp [l]; omega
  have hlow : 2*l≤b := by dsimp [b,l]; omega
  have hres : a=b-2*l ∧ k=2*l+2 := by dsimp [b,l]; omega
  refine ⟨b,l,?_⟩
  simpa only [P,if_neg hb0,if_neg hb1,if_neg hl0,if_pos hlow] using hres

/-- The stopping exponential dominates its linear correction from m=4. -/
private theorem power_ge_linear (m : Nat) (hm : 4≤m) :
    3*m+512 ≤ (2:Nat)^(2*m+2) := by
  have hall : ∀ n:Nat, 3*(n+4)+512 ≤ (2:Nat)^(2*(n+4)+2) := by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
        have he : 2*((n+1)+4)+2=(2*(n+4)+2)+2 := by omega
        rw [he,Nat.pow_add]
        simp only [show (2:Nat)^2=4 by decide]
        omega
  have h := hall (m-4)
  simpa only [show m-4+4=m by omega] using h

/-- The new high-stopping lattice is wholly inside the odd-right
    strict I2-minus-I3 strip, even for its j=2 subfamily. -/
theorem high_stop_strip (j m k : Nat)
    (hm : 4≤m) (hm4 : m%4=0) (hj : (j+m)%32=26)
    (hgate : k+j+3*m+5=(2:Nat)^(2*m+2)*(j+3)) :
    ((2*j+3+k)%32=8 ∧ k%16=9) ∨
    ((2*j+3+k)%32=24 ∧ k%16=1) := by
  have hp32 : 32 ∣ (2:Nat)^(2*m+2) := by
    change (2:Nat)^5 ∣ 2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨q,hq⟩ := hp32
  have hmod : (k+j+3*m+5)%32=0 := by
    apply Nat.mod_eq_zero_of_dvd
    refine ⟨q*(j+3),?_⟩
    calc
      k+j+3*m+5=(2:Nat)^(2*m+2)*(j+3) := hgate
      _=(32*q)*(j+3) := by rw [hq]
      _=32*(q*(j+3)) := by ac_rfl
  by_cases h8 : m%8=0
  · right; omega
  · left; omega

/-- All target size conditions follow from the genuine high-stopping
    equation, without restricting j beyond the modular lattice. -/
theorem high_stop_bounds (j m k : Nat)
    (hm : 4≤m) (hm4 : m%4=0) (hj : (j+m)%32=26)
    (hgate : k+j+3*m+5=(2:Nat)^(2*m+2)*(j+3)) :
    7≤2*j+3 ∧ 512≤k := by
  have hj2 : 2≤j := by omega
  have hpow : 3*m+512 ≤ (2:Nat)^(2*m+2) := power_ge_linear m hm
  have hpow1 : 1≤(2:Nat)^(2*m+2) := Nat.pow_pos (by decide)
  have hjpart : j≤(2:Nat)^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hpow1
  have h3 : 3*(3*m+512)≤3*(2:Nat)^(2*m+2) :=
    Nat.mul_le_mul_left 3 hpow
  have hexp : (2:Nat)^(2*m+2)*(j+3) =
       2^(2*m+2)*j+3*2^(2*m+2) := by
    rw [Nat.mul_add]
    omega
  rw [hexp] at hgate
  constructor <;> omega

#print axioms high_stop_strip
#print axioms high_stop_bounds
#print axioms first_exists
#print axioms second_exists
#print axioms only_first
#print axioms first_parent_residues
#print axioms second_terminal
end BB6.Agent29Simple
