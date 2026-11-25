import WeightedDigitGap
namespace BB6.Agent45WeightedDigitGap
open BB6.Agent45ReverseBlock (corr)
open BB6.Agent45.DelayedCarry (Trace total target target_eq trace_bounds quotient)

theorem corr_extend (k B x : Nat) (hB : B<2^k) (hx : x≤1) :
    corr (k+1) (B+2^k*x)=corr k B+B+2^k*x := by
  induction k generalizing B with
  | zero =>
    have hb : B=0 := by simpa using hB
    subst B
    have hx' : x=0 ∨ x=1 := by omega
    rcases hx' with rfl|rfl <;> decide
  | succ k ih =>
    have hhalf : B/2<2^k := by rw [Nat.pow_succ] at hB; omega
    have hi := ih (B/2) hhalf
    have hp : 2^(k+1)*x=2*(2^k*x) := by rw [Nat.pow_succ]; ac_rfl
    have hd : (B+2^(k+1)*x)/2=B/2+2^k*x := by rw [hp]; omega
    have hm : (B+2^(k+1)*x)%2=B%2 := by rw [hp]; omega
    change 2*corr (k+1) ((B+2^(k+1)*x)/2)+(k+2)*((B+2^(k+1)*x)%2)=corr (k+1) B+B+2^(k+1)*x
    rw [hd,hm,hi,hp]
    change 2*(corr k (B/2)+B/2+2^k*x)+(k+2)*(B%2)=2*corr k (B/2)+(k+1)*(B%2)+B+2*(2^k*x)
    simp only [Nat.add_mul,Nat.one_mul]
    omega

theorem weight_extend (k B x : Nat) (hB : B<2^k) (hx : x≤1) :
    digitWeight (k+1) (B+2^k*x)=digitWeight k B+k*(2^k*x) := by
  have hh := corr_le_mul k B hB
  have hB' : B+2^k*x<2^(k+1) := by
    rw [Nat.pow_succ]
    rcases (show x=0 ∨ x=1 by omega) with h0|h1
    · simp [h0]; omega
    · simp [h1]; omega
  have hc := corr_le_mul (k+1) (B+2^k*x) hB'
  rw [corr_extend k B x hB hx] at hc
  unfold digitWeight
  rw [corr_extend k B x hB hx]
  rw [Nat.add_mul,Nat.one_mul,Nat.mul_add] at hc ⊢
  omega

theorem weight_pad (k j B : Nat) (hB : B<2^k) : digitWeight (k+j) B=digitWeight k B := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hp := Nat.pow_le_pow_right (by decide : 0<2) (show k≤k+j by omega)
    have hh := weight_extend (k+j) B 0 (by omega) (by decide)
    simpa [Nat.add_assoc,ih] using hh

def E (n k B : Nat) : Nat := (n+3)*B+digitWeight k B

theorem E_extend (n k B x : Nat) (hB : B<2^k) (hx : x≤1) :
    E n (k+1) (B+2^k*x)=E n k B+(n+k+3)*(2^k*x) := by
  unfold E
  rw [weight_extend k B x hB hx,Nat.mul_add]
  have he : (n+k+3)*(2^k*x)=(n+3)*(2^k*x)+k*(2^k*x) := by
    rw [show n+k+3=n+3+k by omega,Nat.add_mul]
  omega

theorem total_even (n : Nat) (hn : 0<n) : total n=2*(7*2^(n-1)) := by
  unfold total
  have hh : n=n-1+1 := by omega
  calc
    7*2^n=7*2^(n-1+1) := by rw [←hh]
    _=2*(7*2^(n-1)) := by rw [Nat.pow_succ]; ac_rfl

/-- Exact integer identity for the unchanged delayed-carry source relation. -/
theorem trace_identity {n k B a : Nat} (h : Trace n k B a) (hn : 0<n) (heven : n%2=0) :
    E n k B=2^k*a+(total n*B)%2^k+1 := by
  induction h with
  | first =>
    have hT := total_even n hn
    simp [E,digitWeight,corr,hT]
    omega
  | step i B a x d h hx he ih =>
    have hB := (trace_bounds n i B a h).2.1
    have hT := total_even n hn
    have hp : total n*(B+2^i*x)=total n*B+2^(i+1)*(7*2^(n-1)*x) := by
      rw [Nat.mul_add,Nat.pow_succ]
      congr 1
      rw [hT]
      ac_rfl
    have hmod : (total n*(B+2^i*x))%2^(i+1)=(total n*B)%2^i+2^i*target n i B := by
      rw [hp,Nat.add_mul_mod_self_left,Nat.pow_succ,Nat.mod_mul,target_eq,quotient]
    rw [E_extend n i B x hB hx,ih,hmod]
    have hp' : (n+i+3)*(2^i*x)=2^i*(x*(n+i+3)) := by ac_rfl
    rw [hp',Nat.pow_succ]
    have he' : 2^i*(2*d)+2^i*target n i B = 2^i*a+2^i*(x*(n+i+3)) := by
      calc
        _ = 2^i*(2*d+target n i B) := (Nat.mul_add _ _ _).symm
        _ = 2^i*(a+x*(n+i+3)) := congrArg (fun t : Nat => 2^i*t) he
        _ = _ := Nat.mul_add _ _ _
    have hprod : 2^i*(2*d)=(2^i*2)*d := by ac_rfl
    rw [hprod] at he'
    omega

#print axioms weight_extend
#print axioms trace_identity
end BB6.Agent45WeightedDigitGap
