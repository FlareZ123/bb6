import PrimitivePeriod
namespace BB6.Agent45WeightedDigitGap

private theorem repeat_same (p j U W k : Nat)
    (hp : 0<p) (hj : 0<j) (h : U*(2^j-1)=W*(2^p-1)) :
    U*geom (2^p) (j*k)=W*geom (2^j) (p*k) := by
  have hp2 : 1≤2^p := Nat.succ_le_of_lt (Nat.two_pow_pos p)
  have hj2 : 1≤2^j := Nat.succ_le_of_lt (Nat.two_pow_pos j)
  have hpos : (2:Int)^p-1>0 := by
    have hh : 2≤2^p := by simpa using Nat.pow_le_pow_right (by decide : 0<2) (show 1≤p by omega)
    have hi : (2:Int)≤2^p := by exact_mod_cast hh
    omega
  have hjpos : (2:Int)^j-1>0 := by
    have hh : 2≤2^j := by simpa using Nat.pow_le_pow_right (by decide : 0<2) (show 1≤j by omega)
    have hi : (2:Int)≤2^j := by exact_mod_cast hh
    omega
  have h1 := geom_eq (2^p) (j*k)
  have h2 := geom_eq (2^j) (p*k)
  simp only [Int.natCast_pow] at h1 h2
  have hpow : p*(j*k)=j*(p*k) := by ac_rfl
  rw [←Int.pow_mul] at h1 h2
  change ((2:Int)^p-1)*(geom (2^p) (j*k):Int)=(2:Int)^(p*(j*k))-1 at h1
  change ((2:Int)^j-1)*(geom (2^j) (p*k):Int)=(2:Int)^(j*(p*k))-1 at h2
  rw [hpow] at h1
  have hh := congrArg (fun x : Nat => (x:Int)) h
  simp only [Int.natCast_mul,Int.natCast_sub hp2,Int.natCast_sub hj2,Int.natCast_pow,Int.natCast_one] at hh
  have he : (((2:Int)^p-1)*((2:Int)^j-1))*((U:Int)*(geom (2^p) (j*k):Int)-W*(geom (2^j) (p*k):Int))=0 := by grind
  have hne : ((2:Int)^p-1)*((2:Int)^j-1)≠0 := Int.mul_ne_zero (by omega) (by omega)
  have hzero := (Int.mul_eq_zero.mp he).resolve_left hne
  exact_mod_cast (show (U:Int)*(geom (2^p) (j*k):Int)=W*(geom (2^j) (p*k):Int) by omega)

/-- If the numerator vanishes, every finite repetition satisfies the
    weighted congruence, even without assuming a valid carry trace. -/
theorem congruence_of_zero_numerator (A s p V U t : Nat) (hp : 0<p)
    (hV : V<2^s) (hU : U<2^p) (hzero : periodicNumerator A s p V U=0) :
    let B := V+2^s*(U*geom (2^p) t)
    (2:Int)^(s+p*t) ∣ (digitWeight (s+p*t) B:Int)-(A:Int)*B-1 := by
  let B := V+2^s*(U*geom (2^p) t)
  let m := s+p*t
  let F : Int := (digitWeight m B:Int)-(A:Int)*B-1
  let D : Nat := 2^p-1
  have hp2 : 1≤2^p := Nat.succ_le_of_lt (Nat.two_pow_pos p)
  have hDcast : (D:Int)=(2:Int)^p-1 := by dsimp [D]; rw [Int.natCast_sub hp2,Int.natCast_pow]; rfl
  have hi := periodic_identity A s p V U t hV hU
  change ((2:Int)^p-1)^2*F=periodicNumerator A s p V U+_ at hi
  rw [hzero,Int.zero_add,←hDcast] at hi
  have hd : ((2:Int)^m) ∣ (D:Int)^2*F := ⟨_,hi⟩
  have hh := Int.natAbs_dvd_natAbs.mpr hd
  simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast] at hh
  change 2^m ∣ D^2*F.natAbs at hh
  have hc := (odd_coprime_pow D (mersenne_odd p hp) m).symm
  have hc2 : Nat.Coprime (2^m) (D^2) := by rw [Nat.pow_succ,Nat.pow_one,Nat.coprime_mul_iff_right]; exact ⟨hc,hc⟩
  have h := hc2.dvd_of_dvd_mul_left hh
  have h' : ((2:Int)^m).natAbs ∣ F.natAbs := by simpa [Int.natAbs_pow] using h
  exact Int.natAbs_dvd_natAbs.mp h'

/-- Every rational periodic tail has a nonzero numerator, without a
    primitive-period hypothesis.  Reduce any nonprimitive description. -/
theorem all_numerator_nonzero (A s p V U : Nat) (hp : 0<p) (hV : V<2^s) (hU : U<2^p) :
    periodicNumerator A s p V U≠0 := by
  induction p using Nat.strongRecOn generalizing U with
  | ind p ih =>
    by_cases hprim : Primitive p U
    · exact primitive_numerator_nonzero A s p V U hp hV hU hprim
    unfold Primitive at hprim
    have hex : ∃ j, 0<j ∧ j<p ∧ (2^p-1) ∣ U*(2^j-1) := by
      by_cases he : ∃ j, 0<j ∧ j<p ∧ (2^p-1) ∣ U*(2^j-1)
      · exact he
      · exfalso
        apply hprim
        intro j hj hjp hd
        exact he ⟨j,hj,hjp,hd⟩
    obtain ⟨j,hj,hjp,hd⟩ := hex
    let W := U*(2^j-1)/(2^p-1)
    have hW : U*(2^j-1)=W*(2^p-1) := by
      have hh := Nat.mul_div_cancel' hd
      dsimp [W]; rw [Nat.mul_comm (U*(2^j-1)/(2^p-1))]; exact hh.symm
    have hD : 0<2^p-1 := by
      have hh : 2≤2^p := by simpa using Nat.pow_le_pow_right (by decide : 0<2) (show 1≤p by omega)
      omega
    have hWlt : W<2^j := by
      have hUle : U≤2^p-1 := by omega
      have hh := Nat.mul_le_mul_right (2^j-1) hUle
      rw [hW,Nat.mul_comm (2^p-1)] at hh
      have h := Nat.le_of_mul_le_mul_right hh hD
      have hj2 := Nat.two_pow_pos j
      omega
    intro hzero
    have hnz := ih j hjp W hj hWlt
    let k := (periodicNumerator A s j V W).natAbs+1
    have hk : (periodicNumerator A s j V W).natAbs<2^(s+j*(p*k)) := by
      have h1 : k≤p*k := Nat.le_mul_of_pos_left k hp
      have h2 : p*k≤j*(p*k) := Nat.le_mul_of_pos_left _ hj
      have h3 : k≤s+j*(p*k) := by omega
      have h4 := Nat.lt_two_pow_self (n:=s+j*(p*k))
      dsimp [k] at h3
      omega
    have hsame := repeat_same p j U W k hp hj hW
    have hlen : s+p*(j*k)=s+j*(p*k) := by ac_rfl
    have hc := congruence_of_zero_numerator A s p V U (j*k) hp hV hU hzero
    dsimp only at hc
    rw [hsame,hlen] at hc
    have hI := periodic_identity A s j V W (p*k) hV hWlt
    dsimp only at hI
    obtain ⟨z,hz⟩ := hc
    rw [hz] at hI
    have hd' : ((2:Int)^(s+j*(p*k))) ∣ periodicNumerator A s j V W := by
      refine ⟨((2:Int)^j-1)^2*z-(((digitWeight j W:Int)+((s:Int)-A)*W)*((2:Int)^j-1)+(j:Int)*W*((p*k:Nat)*((2:Int)^j-1)-(2:Int)^j)),?_⟩
      grind
    exact hnz (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd' (by simpa [Int.natAbs_pow] using hk))

/-- A finite repeated delayed trace, of any period, cannot outgrow its
    exact periodic numerator. -/
theorem no_repeated_trace (n A s p V U t a : Nat)
    (hn : 0<n) (heven : n%2=0)
    (hA : BB6.Agent45.DelayedCarry.total n=n+3+A)
    (hp : 0<p) (hV : V<2^s) (hU : U<2^p)
    (hsize : (periodicNumerator A s p V U).natAbs<2^(s+p*t)) :
    ¬ BB6.Agent45.DelayedCarry.Trace n (s+p*t) (V+2^s*(U*geom (2^p) t)) a := by
  intro h
  have hd := trace_periodic_dvd n A s p V U t a hn heven hA hV hU h
  exact all_numerator_nonzero A s p V U hp hV hU (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by simpa [Int.natAbs_pow] using hsize))

#print axioms all_numerator_nonzero
#print axioms no_repeated_trace
end BB6.Agent45WeightedDigitGap
