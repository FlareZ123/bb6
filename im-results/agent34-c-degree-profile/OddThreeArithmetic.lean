import Lean.Elab.Tactic.Omega

namespace BB6.Agent34OddThree

def P (a k x y : Nat) : Prop :=
  if a=0 then
    if k=0 then False
    else if k=1 then x=0 ∧ y=4
    else 4≤y ∧ ∃ n:Nat, x+y=2^n*8 ∧ (2*k+1)+8+3*n=x+2*y
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
    (5≤y ∧ ∃ n:Nat,
      x+y+1=2^n*(2*(a-1)+8) ∧
      (2*k-a+3)+(2*(a-1)+8)+3*n=x+2*y+2)

private theorem div_pow_8 (a n q : Nat) (ha : 2≤a) (he : a%2=0) (hn : 1≤n)
    (hq : q=2^n*(2*(a-1)+6)) : q%8=0 := by
  have hpow : 2 ∣ (2:Nat)^n := by
    have hh : (2:Nat)^1 ∣ (2:Nat)^n := Nat.pow_dvd_pow 2 hn
    simpa using hh
  obtain ⟨p,hp⟩ := hpow
  have hbase : 4 ∣ 2*(a-1)+6 := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  obtain ⟨u,hu⟩ := hbase
  have hd : 8 ∣ q := by
    refine ⟨p*u,?_⟩
    calc
      q = 2^n*(2*(a-1)+6) := hq
      _ = (2*p)*(4*u) := by rw [hp,hu]
      _ = 8*(p*u) := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  exact Nat.mod_eq_zero_of_dvd hd

private theorem div_pow_16 (a n q : Nat) (ha : 2≤a) (he : a%2=0) (hn : 2≤n)
    (hq : q=2^n*(2*(a-1)+6)) : q%16=0 := by
  have hpow : 4 ∣ (2:Nat)^n := by
    have hh : (2:Nat)^2 ∣ (2:Nat)^n := Nat.pow_dvd_pow 2 hn
    simpa using hh
  obtain ⟨p,hp⟩ := hpow
  have hbase : 4 ∣ 2*(a-1)+6 := by
    apply Nat.dvd_of_mod_eq_zero
    omega
  obtain ⟨u,hu⟩ := hbase
  have hd : 16 ∣ q := by
    refine ⟨p*u,?_⟩
    calc
      q = 2^n*(2*(a-1)+6) := hq
      _ = (4*p)*(4*u) := by rw [hp,hu]
      _ = 16*(p*u) := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  exact Nat.mod_eq_zero_of_dvd hd

/-- S=84 mod128, odd y=59 mod64: every first parent is one ordinary n=0 bounce. -/
theorem first_forced (a k x y : Nat)
    (hy : 128≤y) (hs : (x+y)%128=84) (hr : y%64=59)
    (h : P a k x y) :
    a%32=8 ∧ k%32=16 ∧ 2*a+4=x+y ∧ 2*k+a+7=x+2*y := by
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [P,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [P,ha0,hk0,hk1] at h
        omega
      · simp only [P,if_pos ha0,if_neg hk0,if_neg hk1] at h
        obtain ⟨_,n,hpow,_⟩ := h
        have hd : 8 ∣ x+y := by
          refine ⟨2^n,?_⟩
          rw [hpow]
          simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        have hh := Nat.mod_eq_zero_of_dvd hd
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [P,ha0,ha1,hk0] at h
        omega
      · by_cases hk1 : k=1
        · simp [P,ha0,ha1,hk0,hk1] at h
          omega
        · by_cases hk2 : k=2
          · simp [P,ha0,ha1,hk0,hk1,hk2] at h
            omega
          · by_cases hk3 : k=3
            · simp [P,ha0,ha1,hk0,hk1,hk2,hk3] at h
              omega
            · simp only [P,if_neg ha0,if_pos ha1,if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] at h
              rcases h with ⟨he,_⟩ | ⟨_,n,hpow,_⟩
              · omega
              · have hd : 16 ∣ x+y+1 := by
                  refine ⟨2^n,?_⟩
                  rw [hpow]
                  omega
                have hh := Nat.mod_eq_zero_of_dvd hd
                omega
    · have ha2 : 2≤a := by omega
      by_cases hk0 : k=0
      · simp [P,ha0,ha1,hk0] at h
        omega
      · by_cases hlow : 2*k≤a
        · simp [P,ha0,ha1,hk0,hlow] at h
          omega
        · by_cases heven : a%2=0
          · simp only [P,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hlow,if_pos heven] at h
            obtain ⟨_,n,hpow,hcost⟩ := h
            have hn : n=0 := by
              by_cases hzero : n=0
              · exact hzero
              · have hd := div_pow_8 a n (x+y) ha2 heven (by omega) hpow
                omega
            subst n
            simp at hpow hcost
            omega
          · simp only [P,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hlow,if_neg heven] at h
            rcases h with ⟨he,_,_,_⟩ | ⟨_,n,hpow,_⟩
            · omega
            · have hd : 2 ∣ x+y+1 := by
                refine ⟨2^n*(a+3),?_⟩
                calc
                  x+y+1=2^n*(2*(a-1)+8) := hpow
                  _ = 2^n*(2*(a+3)) := by
                    congr 1
                    omega
                  _ = 2*(2^n*(a+3)) := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
              have hh := Nat.mod_eq_zero_of_dvd hd
              omega

/-- Both second predecessors are bad one-step-image targets. -/
theorem second_forced (a k b l : Nat)
    (ha : 128≤a) (hk : 128≤k)
    (ha32 : a%32=8) (hk32 : k%32=16)
    (h : P b l a k) :
    5≤l ∧ l%2=1 ∧ (b+l)%4=1 := by
  by_cases hb0 : b=0
  · by_cases hl0 : l=0
    · simp [P,hb0,hl0] at h
    · by_cases hl1 : l=1
      · simp [P,hb0,hl0,hl1] at h
        omega
      · simp only [P,if_pos hb0,if_neg hl0,if_neg hl1] at h
        obtain ⟨_,n,hpow,_⟩ := h
        by_cases hn : n=0
        · subst n
          simp at hpow
          omega
        · have hpow2 : 2 ∣ (2:Nat)^n := by
            have hd : (2:Nat)^1 ∣ (2:Nat)^n := Nat.pow_dvd_pow 2 (by omega)
            simpa using hd
          obtain ⟨q,hq⟩ := hpow2
          have hd : 16∣a+k := by
            refine ⟨q,?_⟩
            calc
              a+k=2^n*8 := hpow
              _=(2*q)*8 := by rw [hq]
              _=16*q := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          have hh := Nat.mod_eq_zero_of_dvd hd
          omega
  · by_cases hb1 : b=1
    · by_cases hl0 : l=0
      · simp [P,hb0,hb1,hl0] at h
        omega
      · by_cases hl1 : l=1
        · simp [P,hb0,hb1,hl0,hl1] at h
          omega
        · by_cases hl2 : l=2
          · simp [P,hb0,hb1,hl0,hl1,hl2] at h
            omega
          · by_cases hl3 : l=3
            · simp [P,hb0,hb1,hl0,hl1,hl2,hl3] at h
              omega
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
      · simp [P,hb0,hb1,hl0] at h
        omega
      · by_cases hlow : 2*l≤b
        · simp [P,hb0,hb1,hl0,hlow] at h
          omega
        · by_cases heven : b%2=0
          · simp only [P,if_neg hb0,if_neg hb1,if_neg hl0,if_neg hlow,if_pos heven] at h
            obtain ⟨_,n,hpow,hcost⟩ := h
            have hsmall : n≤1 := by
              by_cases hsmall : n≤1
              · exact hsmall
              · have hd := div_pow_16 b n (a+k) hb2 heven (by omega) hpow
                omega
            have hn : n=0 ∨ n=1 := by omega
            rcases hn with h0 | h1
            · subst n
              simp at hpow hcost
              omega
            · subst n
              simp at hpow hcost
              omega
          · simp only [P,if_neg hb0,if_neg hb1,if_neg hl0,if_neg hlow,if_neg heven] at h
            rcases h with ⟨he,_,_,_⟩ | ⟨_,n,hpow,_⟩
            · omega
            · have hd : 2 ∣ a+k+1 := by
                refine ⟨2^n*(b+3),?_⟩
                calc
                  a+k+1=2^n*(2*(b-1)+8) := hpow
                  _=2^n*(2*(b+3)) := by
                    congr 1
                    omega
                  _=2*(2^n*(b+3)) := by simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
              have hh := Nat.mod_eq_zero_of_dvd hd
              omega

/-- This odd-right cylinder really has a first incoming high-bounce edge. -/
theorem first_exists (x y : Nat)
    (hx : 8≤x) (hy : 256≤y)
    (hs : (x+y)%128=84) (hr : y%64=59) :
    ∃ a k, P a k x y ∧ 128≤a ∧ 128≤k ∧ k%2=0 := by
  let a := (x+y-4)/2
  let k := (x+2*y-a-7)/2
  have haeq : 2*a+4=x+y := by dsimp [a]; omega
  have hkeq : 2*k+a+7=x+2*y := by dsimp [k]; omega
  have ha32 : a%32=8 := by omega
  have hk32 : k%32=16 := by omega
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
      · simp
        omega
      · simp
        omega
  exact ⟨a,k,hpre,ha128,hk128,by omega⟩

/-- Every large even right counter has an actual incoming direct edge. -/
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

end BB6.Agent34OddThree
