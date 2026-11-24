import ReverseUnitMap

namespace BB6.Agent9FirstReturn
open BB6P1Unit

def phase (s : Nat) : Nat := if s%3=0 then 1 else if s%3=1 then 2 else 4

def errorBudget (k s : Nat) : Nat := 2^(s+1)*k-k

private theorem budget_zero (k : Nat) : errorBudget k 0=k := by
  simp [errorBudget]; omega

private theorem budget_succ (k s : Nat) :
    errorBudget k (s+1)=2*errorBudget k s+k := by
  unfold errorBudget
  have hh : 2^((s+1)+1)*k=2*(2^(s+1)*k) := by rw [Nat.pow_succ]; ac_rfl
  have hle := Nat.le_mul_of_pos_left k (Nat.two_pow_pos (s+1))
  omega

private theorem budget_le (k s L P : Nat) (hs : s≤L)
    (h : 2^(L+1)*k≤P) : errorBudget k s≤P := by
  have hp := Nat.pow_le_pow_right (show 0<2 by decide) (show s+1≤L+1 by omega)
  have hm := Nat.mul_le_mul_right k hp
  unfold errorBudget
  omega

/-- The first moving-modulus shadow is exactly the 1,2,4 cycle modulo seven,
up to an exponentially growing nonnegative error. -/
theorem shadow_bounds (P k L s : Nat) (hk : 0<k) (hL : L≤k)
    (hbudget : 2^(L+1)*k≤P) (hs : s≤L) :
    P*phase s ≤ run (7*P-k) (P+k) s ∧
    run (7*P-k) (P+k) s ≤ P*phase s+errorBudget k s := by
  have hkp : k≤P := by
    have hle := Nat.le_mul_of_pos_left k (Nat.two_pow_pos (L+1))
    omega
  induction s with
  | zero => simp [run,phase,budget_zero]
  | succ s ih =>
    obtain ⟨hlo,hhi⟩ := ih (by omega)
    have hB := budget_le k (s+1) L P hs hbudget
    rw [budget_succ] at hB
    let r := run (7*P-k) (P+k) s
    let M := 7*P-k+s+1
    have hMlo : 7*P-k≤M := by dsimp [M]; omega
    have hMhi : M≤7*P := by dsimp [M]; omega
    have hMpos : 0<M := by omega
    have hrun : run (7*P-k) (P+k) (s+1)=2*r%M := rfl
    rw [hrun,budget_succ]
    change P*phase s≤r at hlo
    change r≤P*phase s+errorBudget k s at hhi
    by_cases h0 : s%3=0
    · have h1 : (s+1)%3=1 := by omega
      simp [phase,h0] at hlo hhi
      have hlt : 2*r<M := by omega
      simp [phase,h1,Nat.mod_eq_of_lt hlt]
      omega
    · by_cases h1 : s%3=1
      · have h2 : (s+1)%3=2 := by omega
        simp [phase,h1] at hlo hhi
        have hlt : 2*r<M := by omega
        simp [phase,h2,Nat.mod_eq_of_lt hlt]
        omega
      · have h2 : s%3=2 := by omega
        have h3 : (s+1)%3=0 := by omega
        simp [phase,h0,h1] at hlo hhi
        have hge : M≤2*r := by omega
        have hlt : 2*r-M<M := by omega
        rw [Nat.mod_eq_sub_mod hge,Nat.mod_eq_of_lt hlt]
        simp [phase,h3]
        omega

theorem two_mul_le_pow (n : Nat) (hn : 2≤n) : 2*n≤2^n := by
  have h : ∀ j : Nat, 2*(j+2)≤2^(j+2) := by
    intro j
    induction j with
    | zero => decide
    | succ j ih =>
      rw [show j+1+2=j+2+1 by omega, Nat.pow_succ]
      omega
  have hh := h (n-2)
  rw [show n-2+2=n by omega] at hh
  exact hh

private theorem initial_doubling (n q j : Nat) (hq : 4*2^n<q+1)
    (hj : j≤n+2) : run q 1 j=2^j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hp := Nat.pow_le_pow_right (show 0<2 by decide) hj
    rw [show 2^(n+2)=4*2^n by rw [Nat.pow_add]; simp; ac_rfl] at hp
    have hp2 : 2*2^j=2^(j+1) := by rw [Nat.pow_succ]; ac_rfl
    rw [run,unit,ih (by omega),hp2,Nat.mod_eq_of_lt (by omega)]

/-- Right-five first returns are impossible until the initial doubling and
first seven-cycle shadow have enough time to escape. No wrap guards are needed. -/
theorem no_return_shadow (n q k : Nat) (hn : 14≤n)
    (hclock : q+k=7*2^n-n-3) (hk : 0<k)
    (hbudget : 2^(k-(n+2))*k≤2^n) : run q 1 k≠1 := by
  have hdom := two_mul_le_pow n (by omega)
  have hkp : k≤2^n := by
    have hle := Nat.le_mul_of_pos_left k (Nat.two_pow_pos (k-(n+2)))
    omega
  have hq : 4*2^n<q+1 := by omega
  by_cases hearly : k≤n+2
  · rw [initial_doubling n q k hq hearly]
    have hp : 1<2^k := by
      simpa only [Nat.pow_zero] using (Nat.pow_lt_pow_right (show 1<(2:Nat) by decide) hk)
    exact Nat.ne_of_gt hp
  · let P := 2^n
    let L := k-(n+3)
    have hsum : n+3+L=k := by dsimp [L]; omega
    have hL : L≤k := by omega
    have hbud : 2^(L+1)*k≤P := by
      have hh : L+1=k-(n+2) := by dsimp [L]; omega
      rw [hh]; exact hbudget
    have hinit := initial_doubling n q (n+2) hq (by omega)
    have hclock' : q+(n+3)=7*P-k := by dsimp [P]; omega
    have hpow : 2*2^(n+2)=8*P := by
      dsimp [P]; rw [Nat.pow_add]; simp; omega
    have hfirst : run q 1 (n+3)=P+k := by
      rw [show n+3=n+2+1 by omega,run,unit,hinit,hpow]
      have hmod : q+(n+2)+1=7*P-k := by omega
      rw [hmod,Nat.mod_eq_sub_mod (by omega)]
      have hh : 8*P-(7*P-k)=P+k := by omega
      rw [hh,Nat.mod_eq_of_lt (by omega)]
    have hr := run_add q 1 (n+3) L
    rw [hsum,hclock',hfirst] at hr
    have hb := (shadow_bounds P k L L hk hL hbud (by omega)).1
    have hphase : 1≤phase L := by
      by_cases h0 : L%3=0
      · simp [phase,h0]
      · by_cases h1 : L%3=1 <;> simp [phase,h0,h1]
    have hp := Nat.le_mul_of_pos_right P (show 0<phase L by omega)
    have hP : 1<P := by dsimp [P]; omega
    omega

/-- A parameterized cutoff within O(log n) of two times the index. -/
theorem no_return_before_two_n (n q k a : Nat) (hn : 14≤n)
    (hclock : q+k=7*2^n-n-3) (hk : 0<k)
    (ha : 2≤a) (han : a≤n) (hpow : 2*n≤2^a)
    (hcut : k+a≤2*n+2) : run q 1 k≠1 := by
  have hp := Nat.pow_le_pow_right (show 0<2 by decide) (show k-(n+2)≤n-a by omega)
  have hm := Nat.mul_le_mul hp (show k≤2^a by omega)
  rw [← Nat.pow_add, show n-a+a=n by omega] at hm
  exact no_return_shadow n q k hn hclock hk hm

#print axioms shadow_bounds
#print axioms no_return_shadow
#print axioms no_return_before_two_n
end BB6.Agent9FirstReturn
