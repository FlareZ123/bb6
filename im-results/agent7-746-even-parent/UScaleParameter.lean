import UParentBandEnvelope

namespace CascadeUParentBandEnvelope

private theorem u_scale_parameter_unique (t s1 s2 : Nat)
    (h1 : 81*3^t < 14*2^s1 ∧ 14*2^s1 < 112*3^t)
    (h2 : 81*3^t < 14*2^s2 ∧ 14*2^s2 < 112*3^t) : s1=s2 := by
  by_cases heq : s1=s2
  · exact heq
  · by_cases hlt : s1<s2
    · have hp : 2^(s1+1) ≤ 2^s2 := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega)
      have hpow : 2^(s1+1)=2*2^s1 := by rw [Nat.pow_succ]; exact Nat.mul_comm _ _
      rw [hpow] at hp
      have hmul : 28*2^s1 ≤ 14*2^s2 := by
        have hh := Nat.mul_le_mul_left 14 hp
        omega
      have hpos : 0 < 3^t := Nat.pow_pos (by decide : 0 < (3:Nat))
      have hcontra : 162*3^t <112*3^t := by
        calc
          162*3^t = 2*(81*3^t) := by omega
          _ < 2*(14*2^s1) := Nat.mul_lt_mul_of_pos_left h1.1 (by decide)
          _ = 28*2^s1 := by omega
          _ ≤ 14*2^s2 := hmul
          _ < 112*3^t := h2.2
      omega
    · have hlt' : s2<s1 := by omega
      have hp : 2^(s2+1) ≤ 2^s1 := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega)
      have hpow : 2^(s2+1)=2*2^s2 := by rw [Nat.pow_succ]; exact Nat.mul_comm _ _
      rw [hpow] at hp
      have hmul : 28*2^s2 ≤ 14*2^s1 := by
        have hh := Nat.mul_le_mul_left 14 hp
        omega
      have hpos : 0 < 3^t := Nat.pow_pos (by decide : 0 < (3:Nat))
      have hcontra : 162*3^t <112*3^t := by
        calc
          162*3^t = 2*(81*3^t) := by omega
          _ < 2*(14*2^s2) := Nat.mul_lt_mul_of_pos_left h2.1 (by decide)
          _ = 28*2^s2 := by omega
          _ ≤ 14*2^s1 := hmul
          _ < 112*3^t := h1.2
      omega

/-- Every odd U/Q parent determines a unique scale parameter s=n+t-k.
    Its admissibility window is 81·3^t < 14·2^s < 112·3^t. -/
theorem u_odd_parent_scale_window
    (n k t d U : Nat)
    (hlo : 27*2^n < U)
    (hhi : U < 28*2^n)
    (hfac : U=3^(t+3)*d)
    (hband : 6*2^k+1≤2^t*d ∧ 2^t*d≤8*2^k-1) :
    ∃ s, (s+k=n+t ∧ 81*3^t<14*2^s ∧ 14*2^s<112*3^t) ∧
      ∀ s', (s'+k=n+t ∧ 81*3^t<14*2^s' ∧ 14*2^s'<112*3^t) → s'=s := by
  have hpow3 : 3^(t+3)=27*3^t := by
    calc
      3^(t+3) = 3^t*3^3 := by rw [Nat.pow_add]
      _ = 27*3^t := by simp [Nat.mul_comm]
  have hfac' : U=27*(3^t*d) := by rw [hfac,hpow3]; ac_rfl
  have hpow23_all : ∀ t : Nat, 2^t≤3^t := by
    intro t
    induction t with
    | zero => decide
    | succ t ih =>
      calc
        2^(t+1) = 2^t*2 := by rw [Nat.pow_succ]
        _ ≤ 3^t*3 := Nat.mul_le_mul ih (by decide : 2≤3)
        _ = 3^(t+1) := by rw [Nat.pow_succ]
  have hpow23 : 2^t≤3^t := hpow23_all t
  have hxsmall : 27*(2^t*d) <28*2^n := by
    calc
      27*(2^t*d) ≤27*(3^t*d) := Nat.mul_le_mul_left 27 (Nat.mul_le_mul_right d hpow23)
      _ = U := by rw [hfac']
      _ <28*2^n := hhi
  have hklt : k<n := by
    by_cases hklt : k<n
    · exact hklt
    · have hkn' : n≤k := by omega
      have hpow : 2^n≤2^k := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hkn'
      have hbig : 6*2^n+1≤2^t*d := by omega
      omega
  let s := n+t-k
  have hs : s+k=n+t := by dsimp [s]; omega
  have hpowNT : 2^(n+t)=2^s*2^k := by
    calc
      2^(n+t)=2^(s+k) := by congr 1 <;> omega
      _ =2^s*2^k := by rw [Nat.pow_add]
  have hpowAdd : 2^n*2^t=2^(n+t) := by rw [Nat.pow_add]
  have hcross : U*2^t=27*3^t*(2^t*d) := by rw [hfac']; ac_rfl
  have hbandLo : 6*2^k <2^t*d := by omega
  have hbandHi : 2^t*d <8*2^k := by omega
  have hhiMul : U*2^t <28*2^n*2^t :=
    Nat.mul_lt_mul_of_pos_right hhi (Nat.pow_pos (by decide : 0<(2:Nat)))
  have hloMul : 27*2^n*2^t <U*2^t :=
    Nat.mul_lt_mul_of_pos_right hlo (Nat.pow_pos (by decide : 0<(2:Nat)))
  have hlowBandMul : (27*3^t)*(6*2^k) < (27*3^t)*(2^t*d) :=
    Nat.mul_lt_mul_of_pos_left hbandLo (Nat.mul_pos (by decide : 0<(27:Nat)) (Nat.pow_pos (by decide : 0<(3:Nat))))
  have hlowComb : (162*3^t)*2^k < (28*2^s)*2^k := by
    calc
      (162*3^t)*2^k = (27*3^t)*(6*2^k) := by
        have hnum : 162=27*6 := by decide
        rw [hnum]
        ac_rfl
      _ < (27*3^t)*(2^t*d) := hlowBandMul
      _ = U*2^t := hcross.symm
      _ < 28*2^n*2^t := hhiMul
      _ = 28*(2^n*2^t) := by ac_rfl
      _ = 28*2^(n+t) := by rw [hpowAdd]
      _ = 28*(2^s*2^k) := by rw [hpowNT]
      _ = (28*2^s)*2^k := by ac_rfl
  have hlowCancel : 162*3^t <28*2^s := Nat.lt_of_mul_lt_mul_right hlowComb
  have hleft : 81*3^t <14*2^s := by
    have hh : 2*(81*3^t) <2*(14*2^s) := by
      calc
        2*(81*3^t) =162*3^t := by omega
        _ <28*2^s := hlowCancel
        _ =2*(14*2^s) := by omega
    exact Nat.lt_of_mul_lt_mul_left hh
  have hhighBandMul : (27*3^t)*(2^t*d) < (27*3^t)*(8*2^k) :=
    Nat.mul_lt_mul_of_pos_left hbandHi (Nat.mul_pos (by decide : 0<(27:Nat)) (Nat.pow_pos (by decide : 0<(3:Nat))))
  have hhighComb : (27*2^s)*2^k < (216*3^t)*2^k := by
    calc
      (27*2^s)*2^k = 27*(2^s*2^k) := by ac_rfl
      _ = 27*2^(n+t) := by rw [hpowNT]
      _ = 27*(2^n*2^t) := by rw [← hpowAdd]
      _ < U*2^t := by simpa [Nat.mul_assoc] using hloMul
      _ = (27*3^t)*(2^t*d) := hcross
      _ < (27*3^t)*(8*2^k) := hhighBandMul
      _ = (216*3^t)*2^k := by
        have hnum : 216=27*8 := by decide
        rw [hnum]
        ac_rfl
  have hhighCancel : 27*2^s <216*3^t := Nat.lt_of_mul_lt_mul_right hhighComb
  have hright : 14*2^s <112*3^t := by
    have hh : 2^s <8*3^t := by
      have hmul : 27*2^s <27*(8*3^t) := by
        calc
          27*2^s <216*3^t := hhighCancel
          _ =27*(8*3^t) := by omega
      exact Nat.lt_of_mul_lt_mul_left hmul
    calc
      14*2^s <14*(8*3^t) := Nat.mul_lt_mul_of_pos_left hh (by decide : 0<(14:Nat))
      _ =112*3^t := by omega
  refine ⟨s, ⟨hs,hleft,hright⟩, ?_⟩
  intro s' hs'
  rcases hs' with ⟨hsEq',hsLower',hsUpper'⟩
  have heq := u_scale_parameter_unique t s s' ⟨hleft,hright⟩ ⟨hsLower',hsUpper'⟩
  exact heq.symm

/-- Exponent 13 has no admissible dyadic scale at all. -/
theorem no_scale_window_t13 (s : Nat) :
    ¬ (81*3^13 < 14*2^s ∧ 14*2^s < 112*3^13) := by
  intro h
  by_cases hs : s≤23
  · have hp : 2^s≤2^23 := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hs
    have hconst : 14*2^23 <81*3^13 := by decide
    omega
  · have hs' : 24≤s := by omega
    have hp : 2^24≤2^s := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) hs'
    have hconst : 112*3^13 <14*2^24 := by decide
    omega

#print axioms no_scale_window_t13
end CascadeUParentBandEnvelope
