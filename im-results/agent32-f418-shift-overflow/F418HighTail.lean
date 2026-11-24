import F418ReturnBounds

namespace BB6.Agent32F418.ReturnBounds.Prefix

/-- Subtracting a correction smaller than 2^h cannot remove an even
    set bit at h+2 without producing an even bit at h. -/
theorem sub_high_even {x c h : Nat} (hc : c ≤ x) (hs : c < 2^h)
    (he : h%2=0) (hn : NoEven (x-c)) :
    x.testBit (h+2) = false := by
  let y := x-c
  have hxy : x=y+c := by dsimp [y]; omega
  have hp := Nat.two_pow_pos h
  have h1 : y/2^h ≤ x/2^h := Nat.div_le_div_right (by omega)
  have h2 : x/2^h ≤ y/2^h+1 := by
    calc
      x/2^h ≤ (y+2^h)/2^h := Nat.div_le_div_right (by omega)
      _ = y/2^h+1 := Nat.add_div_right y hp
  have h0 : (y/2^h).testBit 0=false := by
    rw [←Nat.testBit_add]
    simpa [y] using hn h he
  have h2b : (y/2^h).testBit 2=false := by
    rw [←Nat.testBit_add]
    simpa [y,Nat.add_comm] using hn (h+2) (by omega)
  rw [show h+2=2+h by omega,Nat.testBit_add]
  simp only [Nat.testBit_eq_decide_div_mod_eq,show 2^0=1 by decide,
    show 2^2=4 by decide,Nat.div_one] at h0 h2b ⊢
  simp only [decide_eq_false_iff_not] at h0 h2b ⊢
  omega

theorem value_div_length (b : Prefix) (Q : Nat) : b.value Q / 2^b.L = Q := by
  obtain ⟨hl,hu⟩ := value_bounds b Q
  apply Nat.div_eq_of_lt_le
  · rw [Nat.mul_comm]; omega
  · rw [Nat.mul_comm]; omega

theorem noBorrow_tail_noEven {b : Prefix} {Q W : Nat}
    (hwidth : b.value Q < 2^W) (hb : b.C ≤ Q)
    (hn : NoEven (b.next Q W)) : NoEven (Q-b.C) := by
  obtain ⟨R,hR,hEq,_⟩ := noBorrow_top hwidth hb
  have hR' : Q-b.C < 2^(W+b.E) :=
    Nat.lt_of_lt_of_le (by have h := (width_tail hwidth).2; omega : Q-b.C < 2^(W-b.L))
      (pow_mono (by omega))
  have hEq' : b.next Q W = 2^(W+b.E)+(Q-b.C) := by unfold next; omega
  intro i hi
  by_cases h : i < W+b.E
  · have ht := hn i hi
    rwa [hEq',Nat.testBit_two_pow_add_gt h] at ht
  · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hR' (pow_mono (by omega)))

/-- A high odd-position 1 in the input excludes an odd-only nonborrow
    output, regardless of the correction's lower-bit borrow pattern. -/
theorem noBorrow_high_odd_exclusion {b : Prefix} {Q W i : Nat}
    (hwidth : b.value Q < 2^W) (hb : b.C ≤ Q)
    (hn : NoEven (b.next Q W)) (hi : i%2=1)
    (hhigh : b.L+b.E+2*b.p+2 ≤ i) :
    (b.value Q).testBit i=false := by
  have hL : b.L%2=1 := by simp [L]
  let h := i-b.L-2
  have he : h%2=0 := by dsimp [h]; omega
  have hc : b.C < 2^h :=
    Nat.lt_of_lt_of_le (correction_upper b) (pow_mono (by dsimp [h]; omega))
  have ht := sub_high_even hb hc he (noBorrow_tail_noEven hwidth hb hn)
  have hie : i=(h+2)+b.L := by dsimp [h]; omega
  rw [hie,Nat.testBit_add,value_div_length]
  exact ht

#print axioms sub_high_even
#print axioms noBorrow_tail_noEven
#print axioms noBorrow_high_odd_exclusion

end BB6.Agent32F418.ReturnBounds.Prefix
