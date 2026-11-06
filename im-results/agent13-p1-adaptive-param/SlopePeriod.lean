import Lean
namespace BB6.Agent13Slope

/-- The slope component of a dyadic inverse-shadow affine lift. -/
inductive SlopePath (P c : Nat) : Nat → Nat → Prop where
| root : SlopePath P c 0 (c*P)
| step {m b} : SlopePath P c m b → (d : Nat) →
    (hd : 2^d ∣ b) →
    SlopePath P c (m+d) (8*P + b/2^d)

/-- Every inverse path carries an integral normal-form numerator, whose
    residue modulo eight is the original feeder's entry multiplier c. -/
theorem slope_normal_form (P c m b : Nat) (h : SlopePath P c m b) :
    ∃ T : Nat, 2^m*b = P*T ∧ T%8=c%8 := by
  induction h with
  | root =>
      refine ⟨c, ?_, ?_⟩
      · simp [Nat.mul_comm]
      · rfl
  | @step m b h d hd ih =>
      rcases ih with ⟨T,hprod,hmod⟩
      rcases hd with ⟨u,hu⟩
      refine ⟨T+8*2^(m+d), ?_, ?_⟩
      · have hb : b/2^d=u := by
          rw [hu]
          exact Nat.mul_div_cancel_left u (Nat.pow_pos (by decide))
        rw [hb]
        calc
          2^(m+d)*(8*P+u) = 8*P*2^(m+d) + 2^m*(2^d*u) := by
            rw [Nat.pow_add]
            simp only [Nat.mul_add]
            ac_rfl
          _ = 8*P*2^(m+d) + P*T := by
            rw [←hu, hprod]
          _ = P*(T+8*2^(m+d)) := by
            rw [Nat.mul_add]
            ac_rfl
      · simp [Nat.add_mod, hmod]

/-- If the normalized feeder numerator has 2-adic depth at least ν,
    a parameter exponent E satisfies every node precision k once
    m+k ≤ E+ν. This is a finite, pathwise sufficient criterion. -/
theorem slope_precision_sufficient
    (P c m b E k ν : Nat)
    (h : SlopePath P c m b)
    (hP : P=2^E)
    (hν : ∀ T : Nat, T%8=c%8 → 2^ν∣T)
    (hbound : m+k≤E+ν) : 2^k∣b := by
  obtain ⟨T,hprod,hres⟩ := slope_normal_form P c m b h
  have hT : 2^ν∣T := hν T hres
  have hlarge : 2^(E+ν)∣P*T := by
    rcases hT with ⟨u,hu⟩
    refine ⟨u, ?_⟩
    rw [hP, hu, Nat.pow_add]
    ac_rfl
  have hsmall : 2^(m+k)∣2^m*b := by
    rw [hprod]
    exact Nat.dvd_trans (Nat.pow_dvd_pow 2 hbound) hlarge
  rcases hsmall with ⟨u,hu⟩
  have hc : 2^m*b = 2^m*(2^k*u) := by
    calc
      2^m*b = 2^(m+k)*u := hu
      _ = 2^m*(2^k*u) := by rw [Nat.pow_add]; ac_rfl
  exact ⟨u, Nat.mul_left_cancel (Nat.pow_pos (by decide)) hc⟩

theorem feeder12_slope_sufficient (E m b k : Nat)
    (h : SlopePath (2^E) 12 m b)
    (hbound : m+k≤E+2) : 2^k∣b := by
  apply slope_precision_sufficient (2^E) 12 m b E k 2 h rfl ?_ hbound
  intro T ht
  have hd : T%4=0 := by omega
  exact Nat.dvd_iff_mod_eq_zero.mpr (by simpa using hd)

theorem feeder10_slope_sufficient (E m b k : Nat)
    (h : SlopePath (2^E) 10 m b)
    (hbound : m+k≤E+1) : 2^k∣b := by
  apply slope_precision_sufficient (2^E) 10 m b E k 1 h rfl ?_ hbound
  intro T ht
  have hd : T%2=0 := by omega
  exact Nat.dvd_iff_mod_eq_zero.mpr (by simpa using hd)

/-- No smaller perturbation period can preserve the required 2^k slope
    precision on a fixed path if its normalized numerator is exactly ν-adic. -/
theorem slope_precision_necessary
    (P c m b E k ν : Nat)
    (h : SlopePath P c m b)
    (hP : P=2^E)
    (hν : ∀ T : Nat, T%8=c%8 → ¬2^(ν+1)∣T)
    (hdiv : 2^k∣b) : m+k≤E+ν := by
  obtain ⟨T,hprod,hres⟩ := slope_normal_form P c m b h
  by_cases hn : m+k≤E+ν
  · exact hn
  exfalso
  have hlarge : E+ν+1≤m+k := by omega
  have hsmall : 2^(m+k)∣2^E*T := by
    rcases hdiv with ⟨u,hu⟩
    refine ⟨u, ?_⟩
    calc
      2^E*T = 2^m*b := by rw [hP] at hprod; exact hprod.symm
      _ = 2^m*(2^k*u) := by rw [hu]
      _ = 2^(m+k)*u := by rw [Nat.pow_add]; ac_rfl
  have hstrong : 2^(E+ν+1)∣2^E*T :=
    Nat.dvd_trans (Nat.pow_dvd_pow 2 hlarge) hsmall
  rcases hstrong with ⟨u,hu⟩
  have hfactor : 2^E*T=2^E*(2^(ν+1)*u) := by
    calc
      _ = 2^(E+ν+1)*u := hu
      _ = 2^E*(2^(ν+1)*u) := by
          have hi : E+ν+1=E+(ν+1) := by omega
          rw [hi, Nat.pow_add]
          ac_rfl
  have heq : T=2^(ν+1)*u := Nat.mul_left_cancel (Nat.pow_pos (by decide)) hfactor
  exact hν T hres ⟨u,heq⟩

theorem feeder12_slope_exact (E m b k : Nat)
    (h : SlopePath (2^E) 12 m b) :
    (2^k∣b) ↔ m+k≤E+2 := by
  constructor
  · intro hd
    apply slope_precision_necessary (2^E) 12 m b E k 2 h rfl ?_ hd
    intro T ht hd8
    have hm8 : T%8=0 := Nat.dvd_iff_mod_eq_zero.mp (by simpa using hd8)
    omega
  · exact feeder12_slope_sufficient E m b k h

theorem feeder10_slope_exact (E m b k : Nat)
    (h : SlopePath (2^E) 10 m b) :
    (2^k∣b) ↔ m+k≤E+1 := by
  constructor
  · intro hd
    apply slope_precision_necessary (2^E) 10 m b E k 1 h rfl ?_ hd
    intro T ht hd4
    have hm4 : T%4=0 := Nat.dvd_iff_mod_eq_zero.mp (by simpa using hd4)
    omega
  · exact feeder10_slope_sufficient E m b k h

#print axioms slope_precision_necessary
#print axioms feeder12_slope_exact
#print axioms feeder10_slope_exact
#print axioms slope_normal_form
#print axioms slope_precision_sufficient
#print axioms feeder12_slope_sufficient
#print axioms feeder10_slope_sufficient
end BB6.Agent13Slope
