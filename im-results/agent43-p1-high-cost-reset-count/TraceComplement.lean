import LagCore

namespace BB6.Agent43P1Complement
open BB6.Agent45.DelayedCarry

/-- The affine reflection changes by one exactly when the delayed first bit
    arrives. Unlike the earlier zero-target fold, this handles all target bits. -/
def cap (n i : Nat) : Nat := n+i+1-(if n<i then 1 else 0)

private theorem even_power (i : Nat) (hi : 1≤i) : 2^i%2=0 := by
  have h := Nat.pow_dvd_pow 2 hi
  exact Nat.dvd_iff_mod_eq_zero.mp (by simpa using h)

private theorem odd_reflect (i B : Nat) (hi : 1≤i) (hB : B<2^i) (ho : B%2=1) :
    (2^i-B)%2=1 := by
  have he : 2^i-B+B=2^i := by omega
  have hm := congrArg (fun a : Nat => a%2) he
  rw [Nat.add_mod,ho,even_power i hi] at hm
  omega

private theorem odd_target_at (n B : Nat) (ho : B%2=1) : target n n B=1 := by
  simp [target,Nat.mul_mod,ho]

/-- The two complementary delayed target words agree in the initial zero
    window and its compulsory one, then have opposite bits forever. -/
theorem target_pair (n i B : Nat) (hn : 1≤n) (hi : 1≤i)
    (hB : B<2^i) (ho : B%2=1) :
    target n i B + target n i (2^i-B) =
      if i<n then 0 else if i=n then 2 else 1 := by
  by_cases hlt : i<n
  · simp [target,hlt]
  by_cases heq : i=n
  · subst i
    rw [odd_target_at n B ho,odd_target_at n (2^n-B) (odd_reflect n B hn hB ho)]
    simp
  have hij : n<i := by omega
  let D := 2^(i-n)
  let X := 7*B
  let Y := 7*(2^i-B)
  have hD : 0<D := Nat.two_pow_pos _
  have hsum : X+Y=D*(7*2^n) := by
    have hb : B+(2^i-B)=2^i := by omega
    have hp : 2^i=D*2^n := by dsimp [D]; rw [←Nat.pow_add]; congr 1; omega
    dsimp [X,Y]
    rw [←Nat.mul_add,hb,hp]
    ac_rfl
  have hXodd : X%2=1 := by dsimp [X]; omega
  have hXrem : X%D≠0 := by
    intro h
    have hdiv : D∣X := Nat.dvd_iff_mod_eq_zero.mpr h
    have h2 : 2∣D := Nat.dvd_iff_mod_eq_zero.mpr (even_power (i-n) (by omega))
    have hbad := Nat.dvd_iff_mod_eq_zero.mp (Nat.dvd_trans h2 hdiv)
    omega
  have hmod : (X%D+Y%D)%D=0 := by
    rw [←Nat.add_mod,hsum,Nat.mul_mod_right]
  have hxr := Nat.mod_lt X hD
  have hyr := Nat.mod_lt Y hD
  have hr : X%D+Y%D=D := by
    by_cases hlt' : X%D+Y%D<D
    · rw [Nat.mod_eq_of_lt hlt'] at hmod
      omega
    · rw [Nat.mod_eq_sub_mod (show X%D+Y%D≥D by omega),Nat.mod_eq_of_lt (show X%D+Y%D-D<D by omega)] at hmod
      omega
  have hdiv := Nat.add_div (a:=X) (b:=Y) hD
  rw [hsum,Nat.mul_div_cancel_left _ hD,if_pos (show D≤X%D+Y%D by omega)] at hdiv
  have hpar : (7*2^n)%2=0 := by rw [Nat.mul_mod,even_power n hn]
  simp only [target,if_neg hlt,if_neg heq]
  change (X/D)%2+(Y/D)%2=1
  omega

/-- The sharper carry range is invariant through the delayed boundary. -/
theorem trace_le_cap (n i B a : Nat) (hn : 1≤n) (h : Trace n i B a) : a≤cap n i := by
  induction h with
  | first => simp [cap,show ¬n<1 by omega]; omega
  | step i B a x c h hx he ih =>
    obtain ⟨hi,hB,ho,_⟩ := trace_bounds n i B a h
    have hy := target_bound n i B
    have hx' : x=0 ∨ x=1 := by omega
    rcases hx' with rfl|rfl <;> simp only [Nat.zero_mul,Nat.one_mul,Nat.add_zero] at he
    all_goals
      by_cases hlt : i<n
      · simp [cap,show ¬n<i by omega,show ¬n<i+1 by omega,target,hlt] at *; omega
      · by_cases heq : i=n
        · have hy1 : target n i B=1 := by rw [heq]; exact odd_target_at n B ho
          simp [cap,show ¬n<i by omega,show n<i+1 by omega,hy1] at *; omega
        · simp [cap,show n<i by omega,show n<i+1 by omega] at *; omega

theorem cap_step (n i B : Nat) (hn : 1≤n) (hi : 1≤i)
    (hB : B<2^i) (ho : B%2=1) :
    2*cap n (i+1)+target n i B+target n i (2^i-B)=cap n i+(n+i+3) := by
  have hp := target_pair n i B hn hi hB ho
  by_cases hlt : i<n
  · simp [cap,hlt,show ¬n<i by omega,show ¬n<i+1 by omega] at *; omega
  · by_cases heq : i=n
    · simp [cap,hlt,heq,show n<n+1 by omega] at *; omega
    · simp [cap,hlt,heq,show n<i by omega,show n<i+1 by omega] at *; omega

/-- Exact involution of the actual delayed-carry Trace, fixing the seed and
    complementing every selected bit after the compulsory initial one. -/
theorem trace_complement (n i B a : Nat) (hn : 1≤n) (heven : n%2=0)
    (h : Trace n i B a) : Trace n i (2^i-B) (cap n i-a) := by
  induction h with
  | first =>
    have hc : cap n 1-(n+2)/2=(n+2)/2 := by simp [cap,show ¬n<1 by omega]; omega
    rw [hc]
    exact Trace.first
  | step i B a x c h hx he ih =>
    obtain ⟨hi,hB,ho,_⟩ := trace_bounds n i B a h
    have ha := trace_le_cap n i B a hn h
    have hc := trace_le_cap n (i+1) (B+2^i*x) c hn (Trace.step i B a x c h hx he)
    have hcap := cap_step n i B hn hi hB ho
    have hw : 2^(i+1)-(B+2^i*x) = 2^i-B+2^i*(1-x) := by
      rw [Nat.pow_succ]
      rcases (show x=0 ∨ x=1 by omega) with rfl|rfl <;> simp <;> omega
    rw [hw]
    refine Trace.step i (2^i-B) (cap n i-a) (1-x) (cap n (i+1)-c) ih (by omega) ?_
    rcases (show x=0 ∨ x=1 by omega) with rfl|rfl <;> simp at he ⊢ <;> omega

/-- At every nontrivial depth it is sufficient to explore B ≡ 1 mod 4.
    Its reflected partner has B ≡ 3 mod 4 and exactly the same existence status. -/
theorem trace_exists_half (n i : Nat) (hn : 1≤n) (heven : n%2=0) (hi : 2≤i) :
    (∃ B a, Trace n i B a) ↔ ∃ B a, Trace n i B a ∧ B%4=1 := by
  constructor
  · rintro ⟨B,a,h⟩
    by_cases hm : B%4=1
    · exact ⟨B,a,h,hm⟩
    obtain ⟨_,hB,ho,_⟩ := trace_bounds n i B a h
    have hpow : 2^i%4=0 := by
      have hd := Nat.pow_dvd_pow 2 hi
      exact Nat.dvd_iff_mod_eq_zero.mp (by simpa using hd)
    have he : 2^i-B+B=2^i := by omega
    have hr := congrArg (fun k : Nat => k%4) he
    rw [Nat.add_mod,hpow] at hr
    have h3 : B%4=3 := by omega
    exact ⟨2^i-B,cap n i-a,trace_complement n i B a hn heven h,by omega⟩
  · rintro ⟨B,a,h,_⟩; exact ⟨B,a,h⟩

#print axioms target_pair
#print axioms trace_le_cap
#print axioms trace_complement
#print axioms trace_exists_half
end BB6.Agent43P1Complement
