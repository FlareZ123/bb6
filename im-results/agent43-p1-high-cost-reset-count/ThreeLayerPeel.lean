import ThreeLayerGap
namespace BB6.Agent43ThreeLayer

/-- Dyadic peeling with a strictly positive remainder below the full power. -/
theorem residue_peel
 (e t K A R : Nat) (hpos : 0<R) (hsmall : R<2^e)
 (heq : K*2^e = A*2^t+R) :
 ∃ d, t≤e ∧ R=2^t*d ∧ K*2^(e-t)=A+d ∧ d≤R ∧ 2^t≤R := by
 have hpowpos : 0<2^e := Nat.pow_pos (by decide)
 have htle : t≤e := by
   by_cases ht : t≤e
   · exact ht
   · exfalso
     have hrev : e≤t := by omega
     have hdiv : 2^e ∣ 2^t := Nat.pow_dvd_pow 2 hrev
     have hleft : 2^e ∣ K*2^e := Nat.dvd_mul_left _ _
     have hright : 2^e ∣ A*2^t := by
       obtain ⟨w,hw⟩ := hdiv
       refine ⟨A*w, ?_⟩
       rw [hw]
       ac_rfl
     have hh := Nat.dvd_sub hleft hright
     have he : K*2^e-A*2^t=R := by omega
     rw [he] at hh
     have hbound := Nat.le_of_dvd hpos hh
     omega
 have hdiv : 2^t ∣ 2^e := Nat.pow_dvd_pow 2 htle
 have hleft : 2^t ∣ K*2^e := by
   obtain ⟨w,hw⟩ := hdiv
   refine ⟨K*w, ?_⟩
   rw [hw]
   ac_rfl
 have hright : 2^t ∣ A*2^t := Nat.dvd_mul_left _ _
 have hh := Nat.dvd_sub hleft hright
 have he : K*2^e-A*2^t=R := by omega
 rw [he] at hh
 obtain ⟨d,hd⟩ := hh
 have hpop : 2^t * 2^(e-t) = 2^e := by
   rw [←Nat.pow_add]
   congr 1
   omega
 have hq : K*2^(e-t)=A+d := by
   have htest : (2^t)*(K*2^(e-t))=(2^t)*(A+d) := by
     calc
       _ = K*2^e := by rw [←hpop]; ac_rfl
       _ = A*2^t+R := heq
       _ = (2^t)*(A+d) := by rw [hd]; simp [Nat.mul_add]; ac_rfl
   exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) htest
 have hle : d≤R := by
   have hpos : 1≤(2:Nat)^t := Nat.one_le_pow t 2 (by decide)
   have hv : d≤(2^t)*d := by simpa using (Nat.mul_le_mul_right d hpos)
   rw [←hd] at hv
   exact hv
 exact ⟨d,htle,hd,hq,hle, Nat.le_of_dvd hpos ⟨d,hd⟩⟩

#print axioms residue_peel
end BB6.Agent43ThreeLayer
