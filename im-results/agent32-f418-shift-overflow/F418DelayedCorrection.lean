import F418SignedQueue

/-! Exact low-bit delay of the correction in a normal F418 return.
    The source-linked return map itself is unchanged. -/
namespace BB6.Agent32F418.ReturnBounds.Prefix

def lastR : Prefix → Nat
  | last r => r
  | more _ t => t.lastR

theorem lastR_le_p (b : Prefix) : b.lastR ≤ b.p := by
  induction b with
  | last r => exact Nat.le_refl _
  | more r t ih => simp [lastR,p]; omega

/-- The correction has exact valuation five times the final half-valuation.
    Earlier collision contributions vanish at all of these low bits. -/
theorem correction_exact_delay (b : Prefix) :
    ∃ u : Nat, u%2=1 ∧ b.C=2^(5*b.lastR)*u := by
  induction b with
  | last r =>
    refine ⟨2^(2*r+2)-1,?_,?_⟩
    · have hp : 2^(2*r+2)=2*2^(2*r+1) := by
        rw [show 2*r+2=(2*r+1)+1 by omega,Nat.pow_succ,Nat.mul_comm]
      have hpos := Nat.two_pow_pos (2*r+1)
      omega
    · simp [C,lastR,Nat.mul_comm]
  | more r t ih =>
    obtain ⟨u,hu,hC⟩ := ih
    let d := 5*t.lastR
    let k := 5*r+3+t.E
    have hd : d<k := by
      have h := lastR_le_p t
      simp [d,k,E]; omega
    have hpow : 2^k=2^d*2^(k-d) := by
      rw [←Nat.pow_add,show d+(k-d)=k by omega]
    have heven : 2^(k-d)=2*2^(k-d-1) := by
      calc
        2^(k-d) = 2^((k-d-1)+1) := congrArg (fun n : Nat => 2^n) (by omega)
        _ = 2*2^(k-d-1) := by rw [Nat.pow_succ,Nat.mul_comm]
    refine ⟨(2^(2*r+3)-1)*2^(k-d)+u,?_,?_⟩
    · rw [heven,show (2^(2*r+3)-1)*(2*2^(k-d-1)) =
        2*((2^(2*r+3)-1)*2^(k-d-1)) by ac_rfl]
      omega
    · change (2^(2*r+3)-1)*2^k+t.C =
        2^d*((2^(2*r+3)-1)*2^(k-d)+u)
      change t.C=2^d*u at hC
      rw [hpow,hC,Nat.mul_add]
      ac_rfl

/-- No high-register injection or correction can change the next low K
    bits in this window. This is an exact all-parameter statement,
    including cases where the full subtraction borrows. -/
theorem next_mod_delay {b : Prefix} {Q W K : Nat}
    (hw : b.value Q<2^W) (hk : K≤5*b.lastR) :
    b.next Q W % 2^K = Q % 2^K := by
  obtain ⟨u,_,hC⟩ := correction_exact_delay b
  have hpow : 2^(5*b.lastR)=2^K*2^(5*b.lastR-K) := by
    rw [←Nat.pow_add,show K+(5*b.lastR-K)=5*b.lastR by omega]
  have hcD : 2^K ∣ b.C := by
    refine ⟨2^(5*b.lastR-K)*u,?_⟩
    rw [hC,hpow,Nat.mul_assoc]
  have hk' : K≤W+b.E := by
    have h := lastR_le_p b
    simp [E]; omega
  have htD : 2^K ∣ 2^(W+b.E) := by
    refine ⟨2^(W+b.E-K),?_⟩
    rw [←Nat.pow_add,show K+(W+b.E-K)=W+b.E by omega]
  have hL := (width_tail hw).1
  have hc : b.C<2^(W+b.E) :=
    Nat.lt_of_lt_of_le (correction_upper b) (pow_mono (by simp [L] at hL; omega))
  have heq : b.next Q W+b.C=2^(W+b.E)+Q := by
    unfold next; omega
  calc
    b.next Q W % 2^K = (b.next Q W+b.C)%2^K := by
      rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hcD, Nat.add_zero, Nat.mod_mod]
    _ = (2^(W+b.E)+Q)%2^K := by rw [heq]
    _ = Q%2^K := by
      rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd htD, Nat.zero_add, Nat.mod_mod]

/-- The next complete Prefix can be read directly from the old high tail
    whenever its entire length is within the delayed-correction window. -/
theorem next_prefix_of_delay {b c : Prefix} {Q W : Nat}
    (hw : b.value Q<2^W) (hL : c.L≤5*b.lastR)
    (hbits : Q%2^c.L=c.value 0) :
    ∃ R : Nat, b.next Q W=c.value R := by
  let N := b.next Q W
  have hmod : N%2^c.L=c.value 0 := (next_mod_delay hw hL).trans hbits
  refine ⟨N/2^c.L,?_⟩
  rw [value_affine]
  have h := Nat.mod_add_div N (2^c.L)
  change N=2^c.L*(N/2^c.L)+c.value 0
  omega

/-- The relay is on the genuine source-connected normal path, not an
    alternative arithmetic orbit. -/
theorem normalPath_relay {b c : Prefix} {Q W : Nat}
    (hp : NormalPath (b.value Q) W) (hL : c.L≤5*b.lastR)
    (hbits : Q%2^c.L=c.value 0) :
    ∃ R : Nat, b.next Q W=c.value R ∧
      NormalPath (c.value R) (W+b.E+1) ∧
      NormalPath (c.next R (W+b.E+1)) (W+b.E+1+c.E+1) := by
  obtain ⟨R,hR⟩ := next_prefix_of_delay (normalPath_safe hp).2 hL hbits
  have h := NormalPath.step hp
  rw [hR] at h
  exact ⟨R,hR,h,NormalPath.step h⟩

/-- A source-gap 7*q+4 with q=1 mod 4 creates a new odd-p emission
    if the source is intact in the protected window.  The preceding
    collision may have had any prefix and any width. -/
theorem odd_gap_relay {b : Prefix} {Q W q : Nat}
    (hp : NormalPath (b.value Q) W) (hq : q%4=1)
    (hL : 7*q+4≤5*b.lastR)
    (hbits : Q%2^(7*q+4)=2^(7*q+3)) :
    let c := Prefix.last ((7*q+3)/2)
    c.p%2=1 ∧ ∃ R : Nat, b.next Q W=c.value R ∧
      NormalPath (c.next R (W+b.E+1)) (W+b.E+1+c.E+1) := by
  let c := Prefix.last ((7*q+3)/2)
  have hcL : c.L=7*q+4 := by simp [c,L_last]; omega
  have hcV : c.value 0=2^(7*q+3) := by
    simp [c,value,show 2*((7*q+3)/2)=7*q+3 by omega]
  have hcP : c.p%2=1 := by simp [c,p]; omega
  have hbits' : Q%2^c.L=c.value 0 := by rw [hcL,hcV]; exact hbits
  have hL' : c.L≤5*b.lastR := hcL ▸ hL
  obtain ⟨R,hR,_,hpath⟩ := normalPath_relay hp hL' hbits'
  exact ⟨hcP,R,hR,hpath⟩

#print axioms correction_exact_delay
#print axioms next_mod_delay
#print axioms next_prefix_of_delay
#print axioms normalPath_relay
#print axioms odd_gap_relay
end BB6.Agent32F418.ReturnBounds.Prefix
