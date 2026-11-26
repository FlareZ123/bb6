import Lean

namespace BB6.Agent32F418.PzeroBlock

def pulses : Nat → Nat
  | 0 => 0
  | j+1 => pulses j + 16^j

def replay (M W : Nat) : Nat → Nat
  | 0 => M
  | j+1 => replay M W j / 2 + 2^(W+3*j+2)

theorem replay_exact (m l W j : Nat) (hj : j≤l) (hl : l≤W) :
    replay (2^l*m) W j = 2^(l-j)*m + 2^(W-j+3)*pulses j := by
  induction j with
  | zero => simp [replay,pulses]
  | succ j ih =>
    rw [replay,ih (by omega)]
    have h1 : l-j = l-(j+1)+1 := by omega
    have h2 : W-j+3 = W-(j+1)+3+1 := by omega
    rw [h1,h2,Nat.pow_succ,Nat.pow_succ]
    have h : 2^(l-(j+1))*2*m+2^(W-(j+1)+3)*2*pulses j =
        (2^(l-(j+1))*m+2^(W-(j+1)+3)*pulses j)*2 := by
      rw [Nat.add_mul]; ac_rfl
    rw [h,Nat.mul_div_cancel _ (by decide : 0<2)]
    have he : W+3*j+2 = W-(j+1)+3+4*j := by omega
    rw [he,Nat.pow_add (a:=2) (m:=W-(j+1)+3) (n:=4*j),pulses,Nat.mul_add]
    have he' : 2^(4*j) = 16^j := by rw [Nat.pow_mul]
    rw [he']; omega

theorem replay_even (m l W j : Nat) (hj : j<l) (hl : l≤W) :
    replay (2^l*m) W j % 2 = 0 := by
  rw [replay_exact m l W j (by omega) hl]
  have h1 : l-j = (l-j-1)+1 := by omega
  have h2 : W-j+3 = (W-j+2)+1 := by omega
  rw [h1,h2,Nat.pow_succ,Nat.pow_succ]
  simp [Nat.add_mod,Nat.mul_mod]

theorem replay_odd (m l W : Nat) (hl : l≤W) (hm : m%2=1) :
    replay (2^l*m) W l % 2 = 1 := by
  rw [replay_exact m l W l (by omega) hl]
  simp only [Nat.sub_self,Nat.pow_zero,Nat.one_mul]
  have h : W-l+3 = W-l+2+1 := by omega
  rw [h,Nat.pow_succ]
  simp [Nat.add_mod,Nat.mul_mod,hm]

theorem replay_terminal (m l W : Nat) (hl : l≤W) :
    replay (2^l*m) W l = m + 2^(W-l+3)*pulses l := by
  rw [replay_exact m l W l (by omega) hl]
  simp

theorem pulses_low (j : Nat) : pulses (j+1)=16*pulses j+1 := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [pulses,ih,Nat.pow_succ]
    have h := ih
    rw [pulses] at h
    omega

theorem pulses_pos {l : Nat} (hl : 0<l) : 0<pulses l := by
  cases l with
  | zero => omega
  | succ l => rw [pulses_low]; omega

/-- Insert m base-four digits 0 or 2, nearest first. -/
def prepend (v : Nat) (m : Nat) (hi : Nat) : Nat :=
  match m with
  | 0 => hi
  | m+1 => 4*prepend (v/2) m hi + 2*(v%2)

def lowWord (v m : Nat) := prepend v m 0

theorem prepend_affine (v m hi : Nat) :
    prepend v m hi = 4^m*hi + lowWord v m := by
  induction m generalizing v with
  | zero => simp [prepend,lowWord]
  | succ m ih =>
    rw [prepend,ih]
    unfold lowWord
    rw [prepend,Nat.pow_succ,Nat.mul_add]
    have he : 4^m*4*hi = 4*(4^m*hi) := by ac_rfl
    rw [he]
    omega

theorem lowWord_bound (v m : Nat) : 3*lowWord v m+2≤2*4^m := by
  induction m generalizing v with
  | zero => simp [lowWord,prepend]
  | succ m ih =>
    have h := ih (v/2)
    change 3*(4*lowWord (v/2) m+2*(v%2))+2≤2*4^(m+1)
    rw [Nat.pow_succ]
    omega

theorem lowWord_injective {v u m : Nat} (hv : v<2^m) (hu : u<2^m)
    (h : lowWord v m = lowWord u m) : v=u := by
  induction m generalizing v u with
  | zero => simp at hv hu; omega
  | succ m ih =>
    change 4*lowWord (v/2) m+2*(v%2)=4*lowWord (u/2) m+2*(u%2) at h
    have hm : v%2=u%2 := by omega
    have hq : lowWord (v/2) m=lowWord (u/2) m := by omega
    rw [Nat.pow_succ] at hv hu
    have he := ih (by omega) (by omega) hq
    omega

theorem lowWord_even (v m : Nat) : lowWord v m%2=0 := by
  cases m <;> simp [lowWord,prepend,Nat.add_mod,Nat.mul_mod]

/-- Generic constructor interface; instantiate OC with original OddChain. -/
def Multi (OC : Nat → Nat → Prop) (N last : Nat) : Prop :=
  ∃ j Q, j%2=1 ∧ 0<Q ∧ N=2^j*(2*Q+1) ∧ OC Q last

theorem multi_pos {OC : Nat → Nat → Prop} {N last : Nat} (h : Multi OC N last) : 0<N := by
  obtain ⟨j,Q,_,hq,rfl,_⟩ := h
  exact Nat.mul_pos (Nat.two_pow_pos _) (by omega)

theorem multi_chain (OC : Nat → Nat → Prop)
    (more : ∀ j Q last, j%2=1 → 0<Q → OC Q last → OC (2^j*(2*Q+1)) last)
    {N last : Nat} (h : Multi OC N last) : OC N last := by
  obtain ⟨j,Q,hj,hq,rfl,hc⟩ := h
  exact more j Q last hj hq hc

theorem multi_prepend (OC : Nat → Nat → Prop)
    (more : ∀ j Q last, j%2=1 → 0<Q → OC Q last → OC (2^j*(2*Q+1)) last)
    {N last : Nat} (h : Multi OC N last) (v m : Nat) : Multi OC (prepend v m N) last := by
  induction m generalizing v with
  | zero => exact h
  | succ m ih =>
    let T := prepend (v/2) m N
    have ht : Multi OC T last := ih (v/2)
    change Multi OC (4*T+2*(v%2)) last
    by_cases hbit : v%2=0
    · obtain ⟨j,Q,hj,hQ,hT,hc⟩ := ht
      refine ⟨j+2,Q,by omega,hQ,?_,hc⟩
      rw [hbit,hT,Nat.mul_zero,Nat.add_zero,Nat.pow_add]
      change 4*(2^j*(2*Q+1)) = (2^j*4)*(2*Q+1)
      ac_rfl
    · have hbit' : v%2=1 := by omega
      refine ⟨1,T,by decide,multi_pos ht,?_,multi_chain OC more ht⟩
      rw [hbit']; omega

theorem pulse_chain (OC : Nat → Nat → Prop)
    (last : ∀ j, j%2=1 → OC (2^j) j)
    (more : ∀ j Q last, j%2=1 → 0<Q → OC Q last → OC (2^j*(2*Q+1)) last)
    (l : Nat) : OC (8*pulses (l+1)) 3 := by
  induction l with
  | zero => exact last 3 (by decide)
  | succ l ih =>
    have h := more 3 (8*pulses (l+1)) 3 (by decide)
      (Nat.mul_pos (by decide) (pulses_pos (by omega))) ih
    rw [pulses_low (l+1)]
    have he : 8*(16*pulses (l+1)+1)=2^3*(2*(8*pulses (l+1))+1) := by omega
    rw [he]
    exact h

theorem pulse_multi (OC : Nat → Nat → Prop)
    (last : ∀ j, j%2=1 → OC (2^j) j)
    (more : ∀ j Q last, j%2=1 → 0<Q → OC Q last → OC (2^j*(2*Q+1)) last)
    (l : Nat) : Multi OC (8*pulses (l+2)) 3 := by
  refine ⟨3,8*pulses (l+1),by decide,Nat.mul_pos (by decide) (pulses_pos (by omega)),?_,pulse_chain OC last more l⟩
  rw [pulses_low (l+1)]; omega

theorem prepared_family (OC : Nat → Nat → Prop)
    (last : ∀ j, j%2=1 → OC (2^j) j)
    (more : ∀ j Q last, j%2=1 → 0<Q → OC Q last → OC (2^j*(2*Q+1)) last)
    (v m l : Nat) (hl : 2≤l) :
    OC (lowWord v m + 2^(2*m+3)*pulses l) 3 := by
  have h := pulse_multi OC last more (l-2)
  rw [show l-2+2=l by omega] at h
  have h' := multi_chain OC more (multi_prepend OC more h v m)
  rw [prepend_affine] at h'
  have he : 4^m*(8*pulses l)=2^(2*m+3)*pulses l := by
    rw [Nat.pow_add,Nat.pow_mul]
    ac_rfl
  rw [he,Nat.add_comm] at h'
  exact h'

def preparedInput (v m l : Nat) := 2^l*(lowWord v m+7)-7

theorem prepared_augmented (v m l : Nat) :
    preparedInput v m l+7=2^l*(lowWord v m+7) := by
  unfold preparedInput
  have h := Nat.mul_le_mul_right (lowWord v m+7) (Nat.two_pow_pos l)
  simp only [Nat.one_mul] at h
  omega

theorem prepared_positive (v m l : Nat) (hl : 2≤l) : 0<preparedInput v m l := by
  have h := prepared_augmented v m l
  have hpow : 4≤2^l := Nat.pow_le_pow_right (by decide : 0<2) hl
  have hmul := Nat.mul_le_mul_right (lowWord v m+7) hpow
  omega

theorem prepared_width (v m l : Nat) (hm : 3≤m) : preparedInput v m l<2^(l+2*m) := by
  have h := lowWord_bound v m
  have hpow : 64≤4^m := Nat.pow_le_pow_right (by decide : 0<4) hm
  have hlt : lowWord v m+7<4^m := by omega
  have hmul := Nat.mul_lt_mul_of_pos_left hlt (Nat.two_pow_pos l)
  rw [←show 2^(2*m)=4^m by rw [Nat.pow_mul],←Nat.pow_add] at hmul
  have he := prepared_augmented v m l
  omega

theorem prepared_injective {v u m l : Nat} (hv : v<2^m) (hu : u<2^m)
    (h : preparedInput v m l=preparedInput u m l) : v=u := by
  have he := (prepared_augmented v m l).symm.trans (congrArg (·+7) h)
  rw [prepared_augmented] at he
  have hlow := (Nat.mul_left_cancel (Nat.two_pow_pos l) he)
  exact lowWord_injective hv hu (by omega)

theorem prepared_endpoint (v m l : Nat) :
    replay (preparedInput v m l+7) (l+2*m) l-7 =
      lowWord v m+2^(2*m+3)*pulses l := by
  rw [prepared_augmented,replay_terminal (lowWord v m+7) l (l+2*m) (by omega)]
  rw [show l+2*m-l+3=2*m+3 by omega]
  omega

#print axioms prepared_positive
#print axioms prepared_width
#print axioms prepared_injective
#print axioms prepared_endpoint
#print axioms pulses_low
#print axioms lowWord_injective
#print axioms prepared_family
#print axioms replay_exact
#print axioms replay_even
#print axioms replay_odd
#print axioms replay_terminal
end BB6.Agent32F418.PzeroBlock
