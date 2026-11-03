import Std
namespace BB6.Agent28

-- A source-independent 2-adic cancellation lemma for exact inverse words.
-- No oddness hypothesis on A is needed.
theorem power_remainder_division (q l A T M : Nat)
    (hMpos : 0 < M) (hMsmall : M < 2^q)
    (heq : 2^l*T + M = A*2^q) : 2^l ∣ M ∧ 2^l ≤ M := by
  by_cases hle : l ≤ q
  · have hpow : (2:Nat)^q = 2^l * 2^(q-l) := by
      calc
        _ = 2^(l+(q-l)) := congrArg (fun e : Nat => (2:Nat)^e) (by omega)
        _ = 2^l*2^(q-l) := Nat.pow_add 2 l (q-l)
    have hLQ : 2^l ∣ 2^q := ⟨2^(q-l), hpow⟩
    have hLA : 2^l ∣ A*2^q := Nat.dvd_trans hLQ (Nat.dvd_mul_left (2^q) A)
    have hLT : 2^l ∣ 2^l*T := Nat.dvd_mul_right (2^l) T
    have hLM : 2^l ∣ M := (Nat.dvd_add_iff_right hLT).mpr (heq ▸ hLA)
    exact ⟨hLM, Nat.le_of_dvd hMpos hLM⟩
  · have hql : q ≤ l := by omega
    have hpow : (2:Nat)^l = 2^q * 2^(l-q) := by
      calc
        _ = 2^(q+(l-q)) := congrArg (fun e : Nat => (2:Nat)^e) (by omega)
        _ = 2^q*2^(l-q) := Nat.pow_add 2 q (l-q)
    have hQL : 2^q ∣ 2^l := ⟨2^(l-q), hpow⟩
    have hQA : 2^q ∣ A*2^q := Nat.dvd_mul_left (2^q) A
    have hQT : 2^q ∣ 2^l*T := Nat.dvd_trans hQL (Nat.dvd_mul_right (2^l) T)
    have hQM : 2^q ∣ M := (Nat.dvd_add_iff_right hQT).mpr (heq ▸ hQA)
    have hbad : 2^q ≤ M := Nat.le_of_dvd hMpos hQM
    omega

#print axioms BB6.Agent28.power_remainder_division
end BB6.Agent28
