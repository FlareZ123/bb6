import ResidueGap

/-!
# Large-valuation gates for three Sheep third-inverse classes

Theorem statements are universal over every valuation a above the stated
cutoff and every exponent e. The core residue-gap lemma is in ResidueGap.lean.
-/

namespace SheepLargeValuation

private theorem exp_grows_minus (m base c : Nat)
    (hbase : m*base < 2^base+c) (hm : m ≤ 2^base) :
    ∀ n, m*(base+n) < 2^(base+n)+c := by
  intro n
  induction n with
  | zero => simpa using hbase
  | succ n ih =>
    have hpowle : 2^base ≤ 2^(base+n) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hstep : m ≤ 2^(base+n) := by omega
    have hpow : 2^(base+(n+1))=2*(2^(base+n)) := by
      rw [show base+(n+1)=(base+n)+1 by omega, Nat.pow_succ]
      omega
    have hlinear : m*(base+(n+1)) = m*(base+n)+m := by
      rw [show base+(n+1)=(base+n)+1 by omega, Nat.mul_add]
      simp
    rw [hpow, hlinear]
    omega

private theorem exp_grows_plus (m base c : Nat)
    (hbase : m*base+c < 2^base) (hm : m ≤ 2^base) :
    ∀ n, m*(base+n)+c < 2^(base+n) := by
  intro n
  induction n with
  | zero => simpa using hbase
  | succ n ih =>
    have hpowle : 2^base ≤ 2^(base+n) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hstep : m ≤ 2^(base+n) := by omega
    have hpow : 2^(base+(n+1))=2*(2^(base+n)) := by
      rw [show base+(n+1)=(base+n)+1 by omega, Nat.pow_succ]
      omega
    have hlinear : m*(base+(n+1)) = m*(base+n)+m := by
      rw [show base+(n+1)=(base+n)+1 by omega, Nat.mul_add]
      simp
    rw [hpow, hlinear]
    omega

private theorem minus_bound (m base c a : Nat) (ha:base≤a)
    (hbase : m*base < 2^base+c) (hm : m≤2^base) :
    m*a-c < 2^a := by
  have h_a : a=base+(a-base) := by omega
  have h := exp_grows_minus m base c hbase hm (a-base)
  rw [h_a]
  by_cases hc : c ≤ m*(base+(a-base))
  · exact (Nat.sub_lt_iff_lt_add hc).mpr (by omega)
  · have hz : m*(base+(a-base))-c=0 := by omega
    rw [hz]
    exact Nat.pow_pos (by decide)

private theorem plus_bound (m base c a : Nat) (ha:base≤a)
    (hbase : m*base+c < 2^base) (hm : m≤2^base) :
    m*a+c < 2^a := by
  obtain ⟨n,rfl⟩ : ∃ n,a=base+n := ⟨a-base,by omega⟩
  exact exp_grows_plus m base c hbase hm n

/-- All large third-inverse valuations for j≡2(mod4) even classes are impossible. -/
theorem evenA1_third_large (a e : Nat) (ha:8≤a) :
    2^e % (2^(a+1)+1) ≠ 30*a-11 := by
  have hd : 30*a-11 < 2^a :=
    minus_bound 30 8 11 a ha (by decide) (by decide)
  exact SheepResidueGap.gap a e (30*a-11) (by omega) (by omega) hd

/-- Large third-inverse valuations for the five even classes mod216. -/
theorem evenA0_third_large (a e : Nat) (ha:7≤a) :
    2^e % (2^(a+1)+1) ≠ 18*a-19 := by
  have hd : 18*a-19 < 2^a :=
    minus_bound 18 7 19 a ha (by decide) (by decide)
  exact SheepResidueGap.gap a e (18*a-19) (by omega) (by omega) hd

/-- Large third-inverse valuations for the seven odd classes mod300. -/
theorem oddA1_third_large (a e : Nat) (ha:9≤a) :
    2^e % (2^(a+1)+1) ≠ 50*a+11 := by
  have hd : 50*a+11 < 2^a :=
    plus_bound 50 9 11 a ha (by decide) (by decide)
  exact SheepResidueGap.gap a e (50*a+11) (by omega) (by omega) hd

#print axioms evenA1_third_large
#print axioms evenA0_third_large
#print axioms oddA1_third_large
end SheepLargeValuation
