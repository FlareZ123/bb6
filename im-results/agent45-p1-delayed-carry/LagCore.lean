import Std
namespace BB6.Agent45.DelayedCarry

def total (n : Nat) := 7*2^n

def quotient (n i B : Nat) := total n*B / 2^i

def target (n i B : Nat) := if i<n then 0 else (7*B / 2^(i-n))%2

theorem target_eq (n i B : Nat) : target n i B = quotient n i B % 2 := by
  unfold target quotient total
  by_cases h : i<n
  · rw [if_pos h]
    have he : n=i+(n-i) := by omega
    have ht : (7*2^n)*B = 2^i*(7*2^(n-i)*B) := by
      have hp : (2:Nat)^n=2^i*2^(n-i) := by rw [← Nat.pow_add]; congr 1 <;> omega
      rw [hp]
      ac_rfl
    rw [ht, Nat.mul_div_cancel_left _ (Nat.two_pow_pos i)]
    have hpow : 2^(n-i) = 2^(n-i-1)*2 := by
      rw [← Nat.pow_succ]; congr 1 <;> omega
    rw [hpow]
    have hpar : 7*(2^(n-i-1)*2)*B=2*(7*2^(n-i-1)*B) := by ac_rfl
    simp [hpar]
  · rw [if_neg h]
    have he : i=n+(i-n) := by omega
    have ht : (7*2^n)*B = 2^n*(7*B) := by ac_rfl
    have hp : (2:Nat)^i = 2^n*2^(i-n) := by
      rw [← Nat.pow_add]; congr 1 <;> omega
    rw [ht,hp,Nat.mul_div_mul_left _ _ (Nat.two_pow_pos n)]

theorem quotient_step (n i B x : Nat) :
    quotient n (i+1) (B+2^i*x) = (quotient n i B + total n*x)/2 := by
  unfold quotient
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  have he : total n*(B+2^i*x) = total n*B + 2^i*(total n*x) := by
    rw [Nat.mul_add]; congr 1; ac_rfl
  rw [he,Nat.add_mul_div_left _ _ (Nat.two_pow_pos i)]

theorem target_bound (n i B : Nat) : target n i B ≤ 1 := by rw [target_eq]; omega

/-- If two words agree in their first s bits, their delayed targets agree
through position n+s-1. -/
theorem target_prefix (n s i B R : Nat) (hi : i<n+s) :
    target n i (B+2^s*R) = target n i B := by
  by_cases h : i<n
  · simp [target,h]
  · simp only [target,if_neg h]
    have hh : i-n<s := by omega
    have hp : (2:Nat)^s = 2^(i-n)*2^(s-(i-n)) := by
      rw [← Nat.pow_add]; congr 1 <;> omega
    have he : 7*(B+2^s*R) = 7*B+2^(i-n)*(7*2^(s-(i-n))*R) := by
      rw [Nat.mul_add,hp]; congr 1; ac_rfl
    rw [he,Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]
    have hp2 : (2:Nat)^(s-(i-n))=2^(s-(i-n)-1)*2 := by
      rw [← Nat.pow_succ]; congr 1 <;> omega
    rw [hp2]
    have hpar : 7*(2^(s-(i-n)-1)*2)*R=2*(7*2^(s-(i-n)-1)*R) := by ac_rfl
    rw [hpar]
    simp

/-- A low word, together with its small arithmetic carry, at each exact cost. -/
inductive Trace (n : Nat) : Nat → Nat → Nat → Prop
  | first : Trace n 1 1 ((n+2)/2)
  | step (i B a x c : Nat) (h : Trace n i B a) (hx : x≤1)
      (he : 2*c+target n i B = a+x*(n+i+3)) :
      Trace n (i+1) (B+2^i*x) c

theorem trace_bounds (n i B a : Nat) (h : Trace n i B a) :
    1≤i ∧ B<2^i ∧ B%2=1 ∧ a≤n+i+2 := by
  induction h with
  | first => simp; omega
  | step i B a x c h hx he ih =>
    obtain ⟨hi,hB,ho,ha⟩ := ih
    have hp : (2:Nat)^i%2=0 := by
      have h := Nat.pow_dvd_pow 2 (show 1≤i by omega)
      exact Nat.dvd_iff_mod_eq_zero.mp (by simpa using h)
    have hx' : x=0 ∨ x=1 := by omega
    rcases hx' with h0|h1
    · subst x; simp [Nat.pow_succ] at *; omega
    · subst x
      simp only [Nat.one_mul, Nat.mul_one] at *
      have hmod : (B+2^i)%2=1 := by rw [Nat.add_mod,ho,hp]
      rw [Nat.pow_succ]
      exact ⟨by omega,by omega,hmod,by omega⟩

/-- Every positive-length word has its unique chronological prefix state. -/
theorem trace_prefix (n i B a : Nat) (h : Trace n i B a) (s : Nat)
    (hs : 1≤s) (hsi : s≤i) :
    ∃ C c R, Trace n s C c ∧ B=C+2^s*R := by
  induction h with
  | first =>
    have hs1 : s=1 := by omega
    subst s
    exact ⟨1,(n+2)/2,0,Trace.first,by simp⟩
  | step i B a x c h hx he ih =>
    by_cases hsi' : s≤i
    · obtain ⟨C,d,R,hC,hB⟩ := ih hsi'
      refine ⟨C,d,R+2^(i-s)*x,hC,?_⟩
      have hp : (2:Nat)^i=2^s*2^(i-s) := by rw [← Nat.pow_add]; congr 1 <;> omega
      rw [hB,hp,Nat.mul_add]; ac_rfl
    · have hs' : s=i+1 := by omega
      subst s
      exact ⟨B+2^i*x,c,0,Trace.step i B a x c h hx he,by simp⟩

end BB6.Agent45.DelayedCarry
