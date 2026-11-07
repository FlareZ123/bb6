import SourcePeriodAllPeriods

/-!
# Pairwise 2-adic separation of P1 source prefixes

For two genuine source ShadowReach paths rooted at different feeder parameters,
a common finite inverse-depth word forces a strong congruence on the parameter
difference.  The proof uses the exact affine identity for a finite depth word;
it does not assume that the family of paths between the two parameters is
affine, periodic, or bounded in depth.
-/

namespace BB6.Precision

open PeriodWord

private theorem coprime_two_three_add_four_mul (w : Nat) :
    Nat.Coprime 2 (3+4*w) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  have hleft := Nat.gcd_dvd_left 2 (3+4*w)
  have hright := Nat.gcd_dvd_right 2 (3+4*w)
  have hgpos : 0 < Nat.gcd 2 (3+4*w) :=
    Nat.gcd_pos_of_pos_left _ (by decide)
  have hgle : Nat.gcd 2 (3+4*w) ≤ 2 :=
    Nat.le_of_dvd (by decide) hleft
  have hgne : Nat.gcd 2 (3+4*w) ≠ 2 := by
    intro heq
    have h2 : 2 ∣ 3+4*w := by rw [← heq]; exact hright
    have hm := Nat.dvd_iff_mod_eq_zero.mp h2
    omega
  omega

private theorem coprime_two_five_add_eight_mul (w : Nat) :
    Nat.Coprime 2 (5+8*w) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  have hleft := Nat.gcd_dvd_left 2 (5+8*w)
  have hright := Nat.gcd_dvd_right 2 (5+8*w)
  have hgpos : 0 < Nat.gcd 2 (5+8*w) :=
    Nat.gcd_pos_of_pos_left _ (by decide)
  have hgle : Nat.gcd 2 (5+8*w) ≤ 2 :=
    Nat.le_of_dvd (by decide) hleft
  have hgne : Nat.gcd 2 (5+8*w) ≠ 2 := by
    intro heq
    have h2 : 2 ∣ 5+8*w := by rw [← heq]; exact hright
    have hm := Nat.dvd_iff_mod_eq_zero.mp h2
    omega
  omega

/-- Two finite runs from feeder 0 with the same depth word have parameter
difference divisible by 2^(cost(word)-2). -/
theorem feeder12_common_word_parameter_divisibility
    (q q' : Nat) (w : List Nat) (z z' : Nat)
    (hqq : q ≤ q')
    (h0 : Run (16*q+8) w 0 (12*q+4) (cost w) z)
    (h1 : Run (16*q'+8) w 0 (12*q'+4) (cost w) z')
    (hM : 2 ≤ cost w) :
    2^(cost w-2) ∣ q'-q := by
  have b0 := PeriodWord.block_affine (16*q+8) w 0 (12*q+4) (cost w) z h0
  have b1 := PeriodWord.block_affine (16*q'+8) w 0 (12*q'+4) (cost w) z' h1
  have hdiff :
      (((2:Nat)^(cost w):Nat):Int) * ((z':Int)-(z:Int)) =
        ((q':Int)-(q:Int)) * (12+16*(weight w:Int)) := by
    calc
      (((2:Nat)^(cost w):Nat):Int) * ((z':Int)-(z:Int)) =
          (((2:Nat)^(cost w):Nat):Int)*(z':Int) -
            (((2:Nat)^(cost w):Nat):Int)*(z:Int) := by grind
      _ = ((12*q'+4:Int)+(weight w:Int)*(16*q'+8:Int)+offset w) -
          ((12*q+4:Int)+(weight w:Int)*(16*q+8:Int)+offset w) := by
            rw [b1,b0]
            grind
      _ = ((q':Int)-(q:Int)) * (12+16*(weight w:Int)) := by grind
  have hqcast : (q:Int) ≤ (q':Int) := by exact_mod_cast hqq
  have hqdiff : 0 ≤ (q':Int)-(q:Int) := by omega
  have hcoef : 0 < (12:Int)+16*(weight w:Int) :=
    Int.add_pos_of_pos_of_nonneg (by decide)
      (Int.mul_nonneg (by decide) (Int.natCast_nonneg _))
  have hprod : 0 ≤ ((q':Int)-(q:Int))*(12+16*(weight w:Int)) :=
    Int.mul_nonneg hqdiff (Int.le_of_lt hcoef)
  have hpow : 0 < (((2:Nat)^(cost w):Nat):Int) := by
    exact_mod_cast (Nat.pow_pos (by decide : 0 < 2))
  have hzdiff : 0 ≤ (z':Int)-(z:Int) := by
    have hm : 0 ≤ (((2:Nat)^(cost w):Nat):Int) * ((z':Int)-(z:Int)) := by
      rw [hdiff]
      exact hprod
    have hm' : 0 ≤ ((z':Int)-(z:Int)) *
        (((2:Nat)^(cost w):Nat):Int) := by
      simpa [Int.mul_comm] using hm
    exact Int.nonneg_of_mul_nonneg_left hm' hpow
  have hzz : z ≤ z' := by exact_mod_cast (Int.le_of_sub_nonneg hzdiff)
  have hEqNat : 2^(cost w) * (z'-z) =
      (q'-q)*(12+16*weight w) := by
    exact_mod_cast hdiff
  have hdiv : 2^(cost w) ∣ (q'-q)*(4*(3+4*weight w)) := by
    refine ⟨z'-z, ?_⟩
    calc
      (q'-q)*(4*(3+4*weight w)) =
          (q'-q)*(12+16*weight w) := by grind
      _ = 2^(cost w)*(z'-z) := hEqNat.symm
  have hpowid : 2^(cost w) = 4*2^(cost w-2) := by
    have he : cost w = 2+(cost w-2) := by omega
    rw [he, Nat.pow_add]
    simp
  rcases hdiv with ⟨k,hk⟩
  have hcancel : 4*((q'-q)*(3+4*weight w)) =
      4*(2^(cost w-2)*k) := by
    calc
      4*((q'-q)*(3+4*weight w)) =
          (q'-q)*(4*(3+4*weight w)) := by grind
      _ = 2^(cost w)*k := hk
      _ = 4*(2^(cost w-2)*k) := by rw [hpowid]; ac_rfl
  have hEq : (q'-q)*(3+4*weight w) = 2^(cost w-2)*k :=
    Nat.mul_left_cancel (by decide) hcancel
  have hdivOdd : 2^(cost w-2) ∣ (q'-q)*(3+4*weight w) := ⟨k,hEq⟩
  exact (Nat.Coprime.pow_left (cost w-2)
    (coprime_two_three_add_four_mul (weight w))).dvd_of_dvd_mul_right hdivOdd

/-- Two finite runs from feeder 1 with the same depth word have parameter
difference divisible by 2^(cost(word)-1). -/
theorem feeder10_common_word_parameter_divisibility
    (q q' : Nat) (w : List Nat) (z z' : Nat)
    (hqq : q ≤ q')
    (h0 : Run (16*q+9) w 0 (10*q+4) (cost w) z)
    (h1 : Run (16*q'+9) w 0 (10*q'+4) (cost w) z')
    (hM : 1 ≤ cost w) :
    2^(cost w-1) ∣ q'-q := by
  have b0 := PeriodWord.block_affine (16*q+9) w 0 (10*q+4) (cost w) z h0
  have b1 := PeriodWord.block_affine (16*q'+9) w 0 (10*q'+4) (cost w) z' h1
  have hdiff :
      (((2:Nat)^(cost w):Nat):Int) * ((z':Int)-(z:Int)) =
        ((q':Int)-(q:Int)) * (10+16*(weight w:Int)) := by
    calc
      (((2:Nat)^(cost w):Nat):Int) * ((z':Int)-(z:Int)) =
          (((2:Nat)^(cost w):Nat):Int)*(z':Int) -
            (((2:Nat)^(cost w):Nat):Int)*(z:Int) := by grind
      _ = ((10*q'+4:Int)+(weight w:Int)*(16*q'+9:Int)+offset w) -
          ((10*q+4:Int)+(weight w:Int)*(16*q+9:Int)+offset w) := by
            rw [b1,b0]
            grind
      _ = ((q':Int)-(q:Int)) * (10+16*(weight w:Int)) := by grind
  have hqcast : (q:Int) ≤ (q':Int) := by exact_mod_cast hqq
  have hqdiff : 0 ≤ (q':Int)-(q:Int) := by omega
  have hcoef : 0 < (10:Int)+16*(weight w:Int) :=
    Int.add_pos_of_pos_of_nonneg (by decide)
      (Int.mul_nonneg (by decide) (Int.natCast_nonneg _))
  have hprod : 0 ≤ ((q':Int)-(q:Int))*(10+16*(weight w:Int)) :=
    Int.mul_nonneg hqdiff (Int.le_of_lt hcoef)
  have hpow : 0 < (((2:Nat)^(cost w):Nat):Int) := by
    exact_mod_cast (Nat.pow_pos (by decide : 0 < 2))
  have hzdiff : 0 ≤ (z':Int)-(z:Int) := by
    have hm : 0 ≤ (((2:Nat)^(cost w):Nat):Int) * ((z':Int)-(z:Int)) := by
      rw [hdiff]
      exact hprod
    have hm' : 0 ≤ ((z':Int)-(z:Int)) *
        (((2:Nat)^(cost w):Nat):Int) := by
      simpa [Int.mul_comm] using hm
    exact Int.nonneg_of_mul_nonneg_left hm' hpow
  have hzz : z ≤ z' := by exact_mod_cast (Int.le_of_sub_nonneg hzdiff)
  have hEqNat : 2^(cost w) * (z'-z) =
      (q'-q)*(10+16*weight w) := by
    exact_mod_cast hdiff
  have hdiv : 2^(cost w) ∣ (q'-q)*(2*(5+8*weight w)) := by
    refine ⟨z'-z, ?_⟩
    calc
      (q'-q)*(2*(5+8*weight w)) =
          (q'-q)*(10+16*weight w) := by grind
      _ = 2^(cost w)*(z'-z) := hEqNat.symm
  have hpowid : 2^(cost w) = 2*2^(cost w-1) := by
    have he : cost w = 1+(cost w-1) := by omega
    rw [he, Nat.pow_add]
    simp
  rcases hdiv with ⟨k,hk⟩
  have hcancel : 2*((q'-q)*(5+8*weight w)) =
      2*(2^(cost w-1)*k) := by
    calc
      2*((q'-q)*(5+8*weight w)) =
          (q'-q)*(2*(5+8*weight w)) := by grind
      _ = 2^(cost w)*k := hk
      _ = 2*(2^(cost w-1)*k) := by rw [hpowid]; ac_rfl
  have hEq : (q'-q)*(5+8*weight w) = 2^(cost w-1)*k :=
    Nat.mul_left_cancel (by decide) hcancel
  have hdivOdd : 2^(cost w-1) ∣ (q'-q)*(5+8*weight w) := ⟨k,hEq⟩
  exact (Nat.Coprime.pow_left (cost w-1)
    (coprime_two_five_add_eight_mul (weight w))).dvd_of_dvd_mul_right hdivOdd

/-- Source-level prefix separation for the authentic feeder 0.  If two
infinite ShadowReach paths start at their exact blank-root feeder states and
share the finite depth word w, then the parameter difference lies in the
single 2-adic cylinder modulo 2^(cost(w)-2). -/
theorem feeder12_common_source_prefix
    (q q' n : Nat) (w : List Nat)
    (p : InfiniteShadowPath (16*q+8) (12*q+4))
    (p' : InfiniteShadowPath (16*q'+8) (12*q'+4))
    (hlen : w.length=n)
    (hdepth0 : ∀ i (hi : i < w.length),
      p.depth (0+i) = w.get ⟨i,hi⟩)
    (hdepth1 : ∀ i (hi : i < w.length),
      p'.depth (0+i) = w.get ⟨i,hi⟩)
    (hm0 : p.m 0=0) (hz0 : p.z 0=12*q+4)
    (hm1 : p'.m 0=0) (hz1 : p'.z 0=12*q'+4)
    (hqq : q≤q') (hM : 2≤cost w) :
    2^(cost w-2) ∣ q'-q := by
  have r0 := p.run_of_list_segment 0 w (by
    intro i hi
    simpa [Nat.zero_add] using hdepth0 i hi)
  have r1 := p'.run_of_list_segment 0 w (by
    intro i hi
    simpa [Nat.zero_add] using hdepth1 i hi)
  have c0 := PeriodWord.run_cost (16*q+8) w (p.m 0) (p.z 0)
      (p.m (0+w.length)) (p.z (0+w.length)) r0
  have c1 := PeriodWord.run_cost (16*q'+8) w (p'.m 0) (p'.z 0)
      (p'.m (0+w.length)) (p'.z (0+w.length)) r1
  have me0 : p.m n=cost w := by
    rw [hlen, Nat.zero_add, hm0] at c0
    simpa using c0
  have me1 : p'.m n=cost w := by
    rw [hlen, Nat.zero_add, hm1] at c1
    simpa using c1
  have r0' : Run (16*q+8) w 0 (12*q+4) (cost w) (p.z n) := by
    rw [hlen, Nat.zero_add] at r0
    simpa [hm0,hz0,me0] using r0
  have r1' : Run (16*q'+8) w 0 (12*q'+4) (cost w) (p'.z n) := by
    rw [hlen, Nat.zero_add] at r1
    simpa [hm1,hz1,me1] using r1
  exact feeder12_common_word_parameter_divisibility
    q q' w (p.z n) (p'.z n) hqq r0' r1' hM

/-- Source-level prefix separation for the authentic feeder 1. -/
theorem feeder10_common_source_prefix
    (q q' n : Nat) (w : List Nat)
    (p : InfiniteShadowPath (16*q+9) (10*q+4))
    (p' : InfiniteShadowPath (16*q'+9) (10*q'+4))
    (hlen : w.length=n)
    (hdepth0 : ∀ i (hi : i < w.length),
      p.depth (0+i) = w.get ⟨i,hi⟩)
    (hdepth1 : ∀ i (hi : i < w.length),
      p'.depth (0+i) = w.get ⟨i,hi⟩)
    (hm0 : p.m 0=0) (hz0 : p.z 0=10*q+4)
    (hm1 : p'.m 0=0) (hz1 : p'.z 0=10*q'+4)
    (hqq : q≤q') (hM : 1≤cost w) :
    2^(cost w-1) ∣ q'-q := by
  have r0 := p.run_of_list_segment 0 w (by
    intro i hi
    simpa [Nat.zero_add] using hdepth0 i hi)
  have r1 := p'.run_of_list_segment 0 w (by
    intro i hi
    simpa [Nat.zero_add] using hdepth1 i hi)
  have c0 := PeriodWord.run_cost (16*q+9) w (p.m 0) (p.z 0)
      (p.m (0+w.length)) (p.z (0+w.length)) r0
  have c1 := PeriodWord.run_cost (16*q'+9) w (p'.m 0) (p'.z 0)
      (p'.m (0+w.length)) (p'.z (0+w.length)) r1
  have me0 : p.m n=cost w := by
    rw [hlen, Nat.zero_add, hm0] at c0
    simpa using c0
  have me1 : p'.m n=cost w := by
    rw [hlen, Nat.zero_add, hm1] at c1
    simpa using c1
  have r0' : Run (16*q+9) w 0 (10*q+4) (cost w) (p.z n) := by
    rw [hlen, Nat.zero_add] at r0
    simpa [hm0,hz0,me0] using r0
  have r1' : Run (16*q'+9) w 0 (10*q'+4) (cost w) (p'.z n) := by
    rw [hlen, Nat.zero_add] at r1
    simpa [hm1,hz1,me1] using r1
  exact feeder10_common_word_parameter_divisibility
    q q' w (p.z n) (p'.z n) hqq r0' r1' hM

/-- If q<q', the common feeder-0 prefix cost cannot exceed the 2-adic
separation scale: 2^(cost(w)-2) ≤ q'-q. -/
theorem feeder12_common_source_prefix_separation
    (q q' n : Nat) (w : List Nat)
    (p : InfiniteShadowPath (16*q+8) (12*q+4))
    (p' : InfiniteShadowPath (16*q'+8) (12*q'+4))
    (hlen : w.length=n)
    (hdepth0 : ∀ i (hi : i < w.length),
      p.depth (0+i) = w.get ⟨i,hi⟩)
    (hdepth1 : ∀ i (hi : i < w.length),
      p'.depth (0+i) = w.get ⟨i,hi⟩)
    (hm0 : p.m 0=0) (hz0 : p.z 0=12*q+4)
    (hm1 : p'.m 0=0) (hz1 : p'.z 0=12*q'+4)
    (hqq : q<q') (hM : 2≤cost w) :
    2^(cost w-2) ≤ q'-q := by
  exact Nat.le_of_dvd (by omega)
    (feeder12_common_source_prefix q q' n w p p' hlen hdepth0
      hdepth1 hm0 hz0 hm1 hz1 (by omega) hM)

/-- If q<q', the common feeder-1 prefix cost cannot exceed the 2-adic
separation scale: 2^(cost(w)-1) ≤ q'-q. -/
theorem feeder10_common_source_prefix_separation
    (q q' n : Nat) (w : List Nat)
    (p : InfiniteShadowPath (16*q+9) (10*q+4))
    (p' : InfiniteShadowPath (16*q'+9) (10*q'+4))
    (hlen : w.length=n)
    (hdepth0 : ∀ i (hi : i < w.length),
      p.depth (0+i) = w.get ⟨i,hi⟩)
    (hdepth1 : ∀ i (hi : i < w.length),
      p'.depth (0+i) = w.get ⟨i,hi⟩)
    (hm0 : p.m 0=0) (hz0 : p.z 0=10*q+4)
    (hm1 : p'.m 0=0) (hz1 : p'.z 0=10*q'+4)
    (hqq : q<q') (hM : 1≤cost w) :
    2^(cost w-1) ≤ q'-q := by
  exact Nat.le_of_dvd (by omega)
    (feeder10_common_source_prefix q q' n w p p' hlen hdepth0
      hdepth1 hm0 hz0 hm1 hz1 (by omega) hM)

private def commonDepthWord (p : InfiniteShadowPath L root) (n : Nat) : List Nat :=
  List.ofFn (fun i : Fin n => p.depth i)

private theorem commonDepthWord_length (p : InfiniteShadowPath L root) (n : Nat) :
    (commonDepthWord p n).length = n := by
  simp [commonDepthWord]

private theorem commonDepthWord_get (p : InfiniteShadowPath L root)
    (n i : Nat) (hi : i<n) :
    (commonDepthWord p n).get
      ⟨i, by simpa [commonDepthWord] using hi⟩ = p.depth i := by
  rw [List.get_eq_getElem]
  simp [commonDepthWord]

private theorem length_le_depth_cost (w : List Nat) : w.length ≤ cost w := by
  induction w with
  | nil => simp [cost]
  | cons t ts ih => simp [cost]; omega

/-- An infinite feeder-0 inverse-depth word determines at most one natural
parameter q.  This follows by applying the finite-prefix separation theorem
to arbitrarily long initial words. -/
theorem feeder12_depth_sequence_parameter_unique
    (q q' : Nat)
    (p : InfiniteShadowPath (16*q+8) (12*q+4))
    (p' : InfiniteShadowPath (16*q'+8) (12*q'+4))
    (hm0 : p.m 0=0) (hz0 : p.z 0=12*q+4)
    (hm1 : p'.m 0=0) (hz1 : p'.z 0=12*q'+4)
    (hdepth : ∀ i, p.depth i = p'.depth i) : q=q' := by
  by_cases heq : q=q'
  · exact heq
  · have hne : q≠q' := heq
    by_cases hqq : q≤q'
    · have hlt : q<q' := by omega
      let d := q'-q
      let n := d+3
      let w := commonDepthWord p n
      have hlen : w.length=n := by simp [w,commonDepthWord,n]
      have hcost : n≤cost w := by
        have h := length_le_depth_cost w
        simpa [hlen] using h
      have hM : 2≤cost w := by omega
      have hdepth0 : ∀ i (hi : i<w.length),
          p.depth (0+i)=w.get ⟨i,hi⟩ := by
        intro i hi
        have hi' : i<n := by simpa [hlen] using hi
        have hg := commonDepthWord_get p n i hi'
        simpa [w,Nat.zero_add] using hg.symm
      have hdepth1 : ∀ i (hi : i<w.length),
          p'.depth (0+i)=w.get ⟨i,hi⟩ := by
        intro i hi
        have hi' : i<n := by simpa [hlen] using hi
        calc
          p'.depth (0+i) = p'.depth i := by simp
          _ = p.depth i := (hdepth i).symm
          _ = w.get ⟨i,hi⟩ := by
            simpa [w] using (commonDepthWord_get p n i hi').symm
      have hdiv := feeder12_common_source_prefix q q' n w p p'
        hlen hdepth0 hdepth1 hm0 hz0 hm1 hz1 hqq hM
      have hpowdvd : 2^(d+1) ∣ 2^(cost w-2) :=
        Nat.pow_dvd_pow 2 (by omega)
      have hsmall : 2^(d+1) ∣ d :=
        Nat.dvd_trans hpowdvd (by simpa [d] using hdiv)
      have hle : 2^(d+1) ≤ d := Nat.le_of_dvd (by omega) hsmall
      have hpow : d < 2^(d+1) := by
        have hh := Nat.lt_pow_self (n:=d+1) (a:=2) (by decide : 1<2)
        omega
      omega
    · have hgt : q'<q := by omega
      let d := q-q'
      let n := d+3
      let w := commonDepthWord p' n
      have hlen : w.length=n := by simp [w,commonDepthWord,n]
      have hcost : n≤cost w := by
        have h := length_le_depth_cost w
        simpa [hlen] using h
      have hM : 2≤cost w := by omega
      have hdepth0 : ∀ i (hi : i<w.length),
          p'.depth (0+i)=w.get ⟨i,hi⟩ := by
        intro i hi
        have hi' : i<n := by simpa [hlen] using hi
        have hg := commonDepthWord_get p' n i hi'
        simpa [w,Nat.zero_add] using hg.symm
      have hdepth1 : ∀ i (hi : i<w.length),
          p.depth (0+i)=w.get ⟨i,hi⟩ := by
        intro i hi
        have hi' : i<n := by simpa [hlen] using hi
        calc
          p.depth (0+i) = p.depth i := by simp
          _ = p'.depth i := hdepth i
          _ = w.get ⟨i,hi⟩ := by
            simpa [w] using (commonDepthWord_get p' n i hi').symm
      have hdiv := feeder12_common_source_prefix q' q n w p' p
        hlen hdepth0 hdepth1 hm1 hz1 hm0 hz0 (by omega) hM
      have hpowdvd : 2^(d+1) ∣ 2^(cost w-2) :=
        Nat.pow_dvd_pow 2 (by omega)
      have hsmall : 2^(d+1) ∣ d :=
        Nat.dvd_trans hpowdvd (by simpa [d] using hdiv)
      have hle : 2^(d+1) ≤ d := Nat.le_of_dvd (by omega) hsmall
      have hpow : d < 2^(d+1) := by
        have hh := Nat.lt_pow_self (n:=d+1) (a:=2) (by decide : 1<2)
        omega
      omega

/-- An infinite feeder-1 inverse-depth word determines at most one natural
parameter q. -/
theorem feeder10_depth_sequence_parameter_unique
    (q q' : Nat)
    (p : InfiniteShadowPath (16*q+9) (10*q+4))
    (p' : InfiniteShadowPath (16*q'+9) (10*q'+4))
    (hm0 : p.m 0=0) (hz0 : p.z 0=10*q+4)
    (hm1 : p'.m 0=0) (hz1 : p'.z 0=10*q'+4)
    (hdepth : ∀ i, p.depth i = p'.depth i) : q=q' := by
  by_cases heq : q=q'
  · exact heq
  · have hne : q≠q' := heq
    by_cases hqq : q≤q'
    · have hlt : q<q' := by omega
      let d := q'-q
      let n := d+2
      let w := commonDepthWord p n
      have hlen : w.length=n := by simp [w,commonDepthWord,n]
      have hcost : n≤cost w := by
        have h := length_le_depth_cost w
        simpa [hlen] using h
      have hM : 1≤cost w := by omega
      have hdepth0 : ∀ i (hi : i<w.length),
          p.depth (0+i)=w.get ⟨i,hi⟩ := by
        intro i hi
        have hi' : i<n := by simpa [hlen] using hi
        have hg := commonDepthWord_get p n i hi'
        simpa [w,Nat.zero_add] using hg.symm
      have hdepth1 : ∀ i (hi : i<w.length),
          p'.depth (0+i)=w.get ⟨i,hi⟩ := by
        intro i hi
        have hi' : i<n := by simpa [hlen] using hi
        calc
          p'.depth (0+i) = p'.depth i := by simp
          _ = p.depth i := (hdepth i).symm
          _ = w.get ⟨i,hi⟩ := by
            simpa [w] using (commonDepthWord_get p n i hi').symm
      have hdiv := feeder10_common_source_prefix q q' n w p p'
        hlen hdepth0 hdepth1 hm0 hz0 hm1 hz1 hqq hM
      have hpowdvd : 2^(d+1) ∣ 2^(cost w-1) :=
        Nat.pow_dvd_pow 2 (by omega)
      have hsmall : 2^(d+1) ∣ d :=
        Nat.dvd_trans hpowdvd (by simpa [d] using hdiv)
      have hle : 2^(d+1) ≤ d := Nat.le_of_dvd (by omega) hsmall
      have hpow : d < 2^(d+1) := by
        have hh := Nat.lt_pow_self (n:=d+1) (a:=2) (by decide : 1<2)
        omega
      omega
    · have hgt : q'<q := by omega
      let d := q-q'
      let n := d+2
      let w := commonDepthWord p' n
      have hlen : w.length=n := by simp [w,commonDepthWord,n]
      have hcost : n≤cost w := by
        have h := length_le_depth_cost w
        simpa [hlen] using h
      have hM : 1≤cost w := by omega
      have hdepth0 : ∀ i (hi : i<w.length),
          p'.depth (0+i)=w.get ⟨i,hi⟩ := by
        intro i hi
        have hi' : i<n := by simpa [hlen] using hi
        have hg := commonDepthWord_get p' n i hi'
        simpa [w,Nat.zero_add] using hg.symm
      have hdepth1 : ∀ i (hi : i<w.length),
          p.depth (0+i)=w.get ⟨i,hi⟩ := by
        intro i hi
        have hi' : i<n := by simpa [hlen] using hi
        calc
          p.depth (0+i) = p.depth i := by simp
          _ = p'.depth i := hdepth i
          _ = w.get ⟨i,hi⟩ := by
            simpa [w] using (commonDepthWord_get p' n i hi').symm
      have hdiv := feeder10_common_source_prefix q' q n w p' p
        hlen hdepth0 hdepth1 hm1 hz1 hm0 hz0 (by omega) hM
      have hpowdvd : 2^(d+1) ∣ 2^(cost w-1) :=
        Nat.pow_dvd_pow 2 (by omega)
      have hsmall : 2^(d+1) ∣ d :=
        Nat.dvd_trans hpowdvd (by simpa [d] using hdiv)
      have hle : 2^(d+1) ≤ d := Nat.le_of_dvd (by omega) hsmall
      have hpow : d < 2^(d+1) := by
        have hh := Nat.lt_pow_self (n:=d+1) (a:=2) (by decide : 1<2)
        omega
      omega

#print axioms feeder12_common_word_parameter_divisibility
#print axioms feeder10_common_word_parameter_divisibility
#print axioms feeder12_common_source_prefix
#print axioms feeder10_common_source_prefix
#print axioms feeder12_common_source_prefix_separation
#print axioms feeder10_common_source_prefix_separation
#print axioms feeder12_depth_sequence_parameter_unique
#print axioms feeder10_depth_sequence_parameter_unique

end BB6.Precision
