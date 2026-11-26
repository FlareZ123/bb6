import Std

namespace BB6.Agent10GroupedGap

structure Segment where
  a : Nat
  b : Nat
  m : Nat
  n : Nat
  next : Nat

def Good (q : Nat) (s : Segment) : Prop :=
  s.n < q ∧ 0 < s.next ∧
  2^s.b * s.next = 3^s.a * (s.n + (2^s.m-1)*q)

/-- The denominator accumulated between two additive gap events is strictly
    smaller than the next power-of-two block capacity. -/
theorem segment_bound {q : Nat} {s : Segment} (h : Good q s) :
    2^s.b < 2^s.m*q := by
  obtain ⟨hn, hp, he⟩ := h
  have hc : (2^s.b).Coprime (3^s.a) :=
    (show Nat.Coprime 2 3 by decide).pow_left _ |>.pow_right _
  have hd : 2^s.b ∣ s.n+(2^s.m-1)*q := by
    apply hc.dvd_of_dvd_mul_left
    exact ⟨s.next, he.symm⟩
  have hpos : 0 < s.n+(2^s.m-1)*q := by
    by_cases hh : s.n+(2^s.m-1)*q=0
    · rw [hh,Nat.mul_zero] at he
      have h := Nat.mul_pos (Nat.two_pow_pos s.b) hp
      omega
    · omega
  have hle := Nat.le_of_dvd hpos hd
  have hm : 1 ≤ 2^s.m := Nat.two_pow_pos _
  have hh : (2^s.m-1)*q+q=2^s.m*q := by
    calc
      _ = (2^s.m-1)*q+1*q := by rw [Nat.one_mul]
      _ = _ := by rw [← Nat.add_mul, Nat.sub_add_cancel hm]
  omega

theorem product_le (q : Nat) (xs : List Segment)
    (h : ∀ s ∈ xs, Good q s) :
    2^((xs.map Segment.b).sum) ≤ 2^((xs.map Segment.m).sum)*q^xs.length := by
  induction xs with
  | nil => simp
  | cons s xs ih =>
    have hs := Nat.le_of_lt (segment_bound (h s (by simp)))
    have ht := ih (fun t hm => h t (by simp [hm]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.pow_add,Nat.pow_succ]
    calc
      2^s.b * 2^((xs.map Segment.b).sum) ≤
          (2^s.m*q) * (2^((xs.map Segment.m).sum)*q^xs.length) := Nat.mul_le_mul hs ht
      _ = 2^s.m * 2^((xs.map Segment.m).sum) * (q^xs.length*q) := by ac_rfl

/-- The strict product bound uses the number of positive-token phases,
    rather than the total length of the primitive valuation word. -/
theorem product_lt (q : Nat) (xs : List Segment) (_hq : 0<q) (hne : xs≠[])
    (h : ∀ s ∈ xs, Good q s) :
    2^((xs.map Segment.b).sum) < 2^((xs.map Segment.m).sum)*q^xs.length := by
  cases xs with
  | nil => contradiction
  | cons s xs =>
    have hs := segment_bound (h s (by simp))
    have ht := product_le q xs (fun t hm => h t (by simp [hm]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.pow_add,Nat.pow_succ]
    calc
      2^s.b * 2^((xs.map Segment.b).sum) <
          (2^s.m*q) * 2^((xs.map Segment.b).sum) :=
            Nat.mul_lt_mul_of_pos_right hs (Nat.two_pow_pos _)
      _ ≤ (2^s.m*q) * (2^((xs.map Segment.m).sum)*q^xs.length) := Nat.mul_le_mul_left _ ht
      _ = 2^s.m * 2^((xs.map Segment.m).sum) * (q^xs.length*q) := by ac_rfl

/-- No full periodic token word can repeat a primitive valuation word with
    exactly one positive valuation, regardless of zero-run length. -/
theorem one_positive_impossible {A L D L0 q : Nat}
    (hD : D≤A) (hL : L0≤L) (hq : q<2^(2*D))
    (h : 2^(A+L+D)<2^L0*q) : False := by
  have h' : 2^(A+L+D)<2^(L0+2*D) := by
    rw [Nat.pow_add 2 L0 (2*D)]
    exact Nat.lt_trans h (Nat.mul_lt_mul_of_pos_left hq (Nat.two_pow_pos _))
  have hh := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp h'
  omega

/-- Integer version of the slope-product estimate, with no logarithms. -/
theorem slope_exponent {S D : Nat} (h : 2^(S+D)<3^S) : 5*D<3*S := by
  have h' : 2^((S+D)*5)<2^(8*S) := by
    calc
      2^((S+D)*5) = (2^(S+D))^5 := Nat.pow_mul _ _ _
      _ < (3^S)^5 := Nat.pow_lt_pow_left h (by decide)
      _ = (3^5)^S := by rw [← Nat.pow_mul, Nat.mul_comm S 5, Nat.pow_mul]
      _ ≤ (2^8)^S := Nat.pow_le_pow_left (by decide) _
      _ = 2^(8*S) := (Nat.pow_mul _ _ _).symm
  have hh := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp h'
  omega

/-- With two positive phases, combine the grouped gap product and the
    first-difference denominator bound. -/
theorem two_gap_bound {S D L0 q r : Nat}
    (hq : q<2^D*r) (h : 2^(S+D)<2^L0*q^2) :
    2^S < 2^(L0+D)*r^2 := by
  apply Nat.lt_of_mul_lt_mul_left (a:=2^D)
  calc
    2^D*2^S = 2^(S+D) := by rw [Nat.pow_add,Nat.mul_comm]
    _ < 2^L0*q^2 := h
    _ < 2^L0*(2^D*r)^2 := Nat.mul_lt_mul_of_pos_left
      (Nat.pow_lt_pow_left hq (by decide)) (Nat.two_pow_pos _)
    _ = 2^D*(2^(L0+D)*r^2) := by
      rw [Nat.mul_pow,Nat.pow_add,show (2^D)^2=2^D*2^D by rw [Nat.pow_succ,Nat.pow_one]]
      ac_rfl

theorem two_gap_fifth {S D L0 r : Nat}
    (h : 2^S<2^(L0+D)*r^2) : 2^(5*S)<2^(5*(L0+D))*r^10 := by
  have hp := Nat.pow_lt_pow_left h (show 5≠0 by decide)
  rw [Nat.mul_pow,← Nat.pow_mul,← Nat.pow_mul,← Nat.pow_mul] at hp
  simpa only [Nat.mul_comm S 5,Nat.mul_comm (L0+D) 5] using hp

theorem two_gap_reduced {S D L0 r : Nat}
    (h : 2^S<2^(L0+D)*r^2) (hd : 5*D<3*S) :
    2^(2*S)<2^(5*L0)*r^10 := by
  have hf := two_gap_fifth h
  have hm : 2^(5*(L0+D))≤2^(5*L0+3*S) := Nat.pow_le_pow_right (by decide) (by omega)
  apply Nat.lt_of_mul_lt_mul_left (a:=2^(3*S))
  calc
    2^(3*S)*2^(2*S) = 2^(5*S) := by rw [← Nat.pow_add]; congr 1; omega
    _ < 2^(5*(L0+D))*r^10 := hf
    _ ≤ 2^(5*L0+3*S)*r^10 := Nat.mul_le_mul_right _ hm
    _ = 2^(3*S)*(2^(5*L0)*r^10) := by rw [Nat.pow_add]; ac_rfl

/-- Two positive valuations in the primitive valuation word permit at most
    seven repetitions, even if arbitrarily many zero valuations intervene. -/
theorem two_positive_repeat_le_seven {A0 L0 b D q r : Nat}
    (hL : 0<L0) (hA : 0<A0)
    (hq : q<2^D*r)
    (hg : 2^(b*(A0+L0)+D)<2^L0*q^2)
    (hs : 2^(b*(A0+L0)+D)<3^(b*(A0+L0)))
    (hr : r<2^(A0+L0) ∨ r<3^A0) : b≤7 := by
  have h := two_gap_reduced (two_gap_bound hq hg) (slope_exponent hs)
  by_cases hb : b≤7
  · exact hb
  have hb8 : 8≤b := by omega
  have hS := Nat.mul_le_mul_right (A0+L0) hb8
  rcases hr with hr|hr
  · have hr' : r^10≤2^(10*(A0+L0)) := by
      calc
        r^10 ≤ (2^(A0+L0))^10 := Nat.pow_le_pow_left (Nat.le_of_lt hr) _
        _ = 2^(10*(A0+L0)) := by rw [Nat.mul_comm 10 (A0+L0),Nat.pow_mul]
    have hh : 2^(2*(b*(A0+L0)))<2^(5*L0+10*(A0+L0)) := by
      rw [Nat.pow_add 2 (5*L0) _]
      exact Nat.lt_of_lt_of_le h (Nat.mul_le_mul_left _ hr')
    have he := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp hh
    omega
  · have hr' : r^10≤2^(16*A0) := by
      calc
        r^10 ≤ (3^A0)^10 := Nat.pow_le_pow_left (Nat.le_of_lt hr) _
        _ = (3^10)^A0 := by rw [← Nat.pow_mul,Nat.mul_comm A0 10,Nat.pow_mul]
        _ ≤ (2^16)^A0 := Nat.pow_le_pow_left (by decide) _
        _ = 2^(16*A0) := (Nat.pow_mul _ _ _).symm
    have hh : 2^(2*(b*(A0+L0)))<2^(5*L0+16*A0) := by
      rw [Nat.pow_add 2 (5*L0) _]
      exact Nat.lt_of_lt_of_le h (Nat.mul_le_mul_left _ hr')
    have he := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp hh
    omega

#print axioms segment_bound
#print axioms product_lt
#print axioms one_positive_impossible
#print axioms two_positive_repeat_le_seven

end BB6.Agent10GroupedGap
