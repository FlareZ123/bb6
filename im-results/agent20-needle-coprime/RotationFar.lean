import RotationValuation

namespace NeedleRotation

/-- Two terms supported at exponents ≥ B cannot cancel a smaller nonzero constant. -/
theorem isolated_constant_nonzero (C U V : Int) (p q B : Nat)
    (hp : B≤p) (hq : B≤q) (hC : C≠0) (hbound : C.natAbs<2^B) :
    C+U*2^p+V*2^q≠0 := by
  intro heq
  have hpow (n : Nat) (hn : B≤n) : (2:Int)^B ∣ (2:Int)^n := by
    apply Int.natAbs_dvd_natAbs.mp
    simp only [Int.natAbs_pow]
    exact Nat.pow_dvd_pow 2 hn
  have h1 : (2:Int)^B ∣ U*2^p := Int.dvd_mul_of_dvd_right (hpow p hp)
  have h2 : (2:Int)^B ∣ V*2^q := Int.dvd_mul_of_dvd_right (hpow q hq)
  have hCeq : C=-(U*2^p+V*2^q) := by omega
  have hCdvd : (2:Int)^B ∣ C := by rw [hCeq,Int.dvd_neg]; exact Int.dvd_add h1 h2
  apply hC
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hCdvd (by simpa using hbound)

/-- A rotation that isolates one of three nonzero terms at residue zero, with
both other residues in [B,m-B], excludes divisibility. -/
theorem three_isolated_no_dvd (m B h : Nat) (t u v : Term)
    (hm : B≤m) (hB : 0<B)
    (ht : t.1≠0) (hz : (rotateTerm m h t).2=0)
    (hu : B≤(rotateTerm m h u).2 ∧ (rotateTerm m h u).2≤m-B)
    (hv : B≤(rotateTerm m h v).2 ∧ (rotateTerm m h v).2≤m-B)
    (hmass : mass (rotate m h [t,u,v])<2^B) :
    ¬ denominator m ∣ value [t,u,v] := by
  intro hd
  have he : ∀ s ∈ rotate m h [t,u,v], s.2≤m-B := by
    intro s hs
    simp [rotate] at hs
    rcases hs with rfl|rfl|rfl
    · omega
    · exact hu.2
    · exact hv.2
  have hzero := rotation_zero_of_gap m B h [t,u,v] hm he hmass hd
  have ht0 : (rotateTerm m h t).1≠0 := by
    simp [rotateTerm,Int.mul_eq_zero,ht,Int.pow_ne_zero (by decide : (-3:Int)≠0)]
  have htbound : (rotateTerm m h t).1.natAbs<2^B := by
    rcases h1 : rotateTerm m h t with ⟨c,e⟩
    rcases h2 : rotateTerm m h u with ⟨d,f⟩
    rcases h3 : rotateTerm m h v with ⟨g,k⟩
    simp only [rotate,List.map_cons,List.map_nil,h1,h2,h3,mass] at hmass
    simp only [h1]
    omega
  have hnon := isolated_constant_nonzero (rotateTerm m h t).1 (rotateTerm m h u).1 (rotateTerm m h v).1
    (rotateTerm m h u).2 (rotateTerm m h v).2 B hu.1 hv.1 ht0 htbound
  apply hnon
  rcases h1 : rotateTerm m h t with ⟨c,e⟩
  rcases h2 : rotateTerm m h u with ⟨d,f⟩
  rcases h3 : rotateTerm m h v with ⟨g,k⟩
  simp only [h1,Prod.snd] at hz
  simp only [rotate,List.map_cons,List.map_nil,h1,h2,h3,value,hz,Int.pow_zero,Int.mul_one,Int.add_zero] at hzero
  simp only [h1,h2,h3]
  omega

/-- A three-term sum with nonzero coefficients at raw exponents 0 and a,
where a and m-a are each at least 2B, has an isolating rotation. -/
theorem three_far_no_dvd (m B a e : Nat) (C U V : Int)
    (hB : 0<B) (ha : 2*B≤a) (hm : a+2*B≤m)
    (hC : C≠0) (hU : U≠0)
    (hmass : ∀ h<m, mass (rotate m h [(C,0),(U,a),(V,e)])<2^B) :
    ¬ denominator m ∣ value [(C,0),(U,a),(V,e)] := by
  have hm0 : 0<m := by omega
  have hlt : a<m := by omega
  let t := e%m
  have ht : t<m := Nat.mod_lt _ hm0
  by_cases hgood : B≤t ∧ t≤m-B
  · exact three_isolated_no_dvd m B 0 (C,0) (U,a) (V,e) (by omega) hB hC
      (by simp [rotateTerm]) (by simp [rotateTerm,Nat.mod_eq_of_lt hlt]; omega)
      (by simpa [rotateTerm,t] using hgood) (hmass 0 hm0)
  · intro hd
    let h := m-a
    have hh : h<m := by dsimp [h]; omega
    have hzero : (a+h)%m=0 := by
      have he : a+h=m := by dsimp [h]; omega
      rw [he,Nat.mod_self]
    have heq : (e+h)%m=(t+h)%m := by rw [Nat.mod_add_mod]
    have hrange : B≤(e+h)%m ∧ (e+h)%m≤m-B := by
      rw [heq]
      by_cases hlow : t<B
      · have hsmall : t+h<m := by dsimp [h]; omega
        rw [Nat.mod_eq_of_lt hsmall]
        dsimp [h]
        omega
      · have hhigh : m-B<t := by omega
        have hlarge : m≤t+h := by dsimp [h]; omega
        have hsmall : t+h-m<m := by omega
        rw [Nat.mod_eq_sub_mod hlarge,Nat.mod_eq_of_lt hsmall]
        dsimp [h]
        omega
    have hmass' : mass (rotate m h [(U,a),(C,0),(V,e)])<2^B := by
      have hx := hmass h hh
      simp only [rotate,List.map_cons,List.map_nil,rotateTerm,mass] at *
      omega
    have hd' : denominator m ∣ value [(U,a),(C,0),(V,e)] := by
      have hv : value [(U,a),(C,0),(V,e)]=value [(C,0),(U,a),(V,e)] := by simp [value]; omega
      rw [hv]
      exact hd
    exact three_isolated_no_dvd m B h (U,a) (C,0) (V,e) (by omega) hB hU
      (by simpa [rotateTerm] using hzero) (by simp [rotateTerm,Nat.mod_eq_of_lt hh]; dsimp [h]; omega)
      (by simpa [rotateTerm] using hrange) hmass' hd'

#print axioms three_far_no_dvd
end NeedleRotation
