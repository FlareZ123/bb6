import RotationCore

namespace NeedleRotation

/-- An odd coefficient at the unique smallest exponent cannot cancel. -/
theorem three_odd_min (u v w : Int) (x y z : Nat)
    (hu : u % 2 = 1) (hxy : x < y) (hxz : x < z) :
    u*2^x + v*2^y + w*2^z ≠ 0 := by
  intro h
  obtain ⟨p,hp⟩ : ∃ p : Nat, y=x+1+p := ⟨y-x-1,by omega⟩
  obtain ⟨q,hq⟩ : ∃ q : Nat, z=x+1+q := ⟨z-x-1,by omega⟩
  rw [hp,hq] at h
  simp only [Int.pow_add,Int.pow_one] at h
  have he : (2:Int)^x * (u + 2*(v*2^p+w*2^q))=0 := by grind
  have hpow : (2:Int)^x ≠ 0 := Int.pow_ne_zero (by decide)
  have heq := (Int.mul_eq_zero.mp he).resolve_left hpow
  omega

theorem three_odd_distinct (u v w : Int) (x y z : Nat)
    (hu : u%2=1) (hv : v%2=1) (hw : w%2=1)
    (hxy : x≠y) (hxz : x≠z) (hyz : y≠z) :
    u*2^x+v*2^y+w*2^z ≠ 0 := by
  by_cases hx : x<y ∧ x<z
  · exact three_odd_min u v w x y z hu hx.1 hx.2
  by_cases hy : y<x ∧ y<z
  · have h := three_odd_min v u w y x z hv hy.1 hy.2
    intro he
    apply h
    omega
  have hz : z<x ∧ z<y := by omega
  have h := three_odd_min w u v z x y hw hz.1 hz.2
  intro he
  apply h
  omega

/-- Rotation preserves oddness of the odd part of a signed coefficient. -/
theorem odd_neg_three_pow (q : Nat) : ((-3:Int)^q)%2=1 := by
  induction q with
  | zero => decide
  | succ q ih => rw [Int.pow_succ, Int.mul_emod, ih]; decide

theorem odd_mul_neg_three_pow (u : Int) (q : Nat) (hu : u%2=1) :
    (u*(-3)^q)%2=1 := by
  rw [Int.mul_emod, hu, odd_neg_three_pow]; decide

/-- Distinct adjusted exponent residues remain distinct after a common rotation. -/
theorem adjusted_distinct (m h e f x y : Nat)
    (hm : 0<m) (hne : (e+x)%m ≠ (f+y)%m) :
    (e+h)%m+x ≠ (f+h)%m+y := by
  intro he
  have hh := congrArg (fun n : Nat => n%m) he
  have he1 : ((e+h)%m+x)%m=(e+x+h)%m := by
    rw [Nat.add_mod ((e+h)%m) x m, Nat.mod_mod]
    rw [←Nat.add_mod]
    congr 1
    omega
  have he2 : ((f+h)%m+y)%m=(f+y+h)%m := by
    rw [Nat.add_mod ((f+h)%m) y m, Nat.mod_mod]
    rw [←Nat.add_mod]
    congr 1
    omega
  rw [he1,he2] at hh
  have hh2 := congrArg (fun n : Nat => (n+(m-h%m))%m) hh
  have hc (t : Nat) : ((t+h)%m+(m-h%m))%m=t%m := by
    rw [Nat.mod_add_mod, Nat.add_assoc, ←Nat.add_mod_mod t (h+(m-h%m)) m]
    have hs : (h+(m-h%m))%m=0 := by
      rw [←Nat.mod_add_mod h m (m-h%m)]
      have heq : h%m+(m-h%m)=m := by have := Nat.mod_lt h hm; omega
      rw [heq, Nat.mod_self]
    rw [hs, Nat.add_zero]
  rw [hc, hc] at hh2
  exact hne hh2

/-- A three-term polynomial cannot be divisible when a mass-bound rotation exists
and the three binary-valuation-adjusted exponent residues are distinct. -/
theorem three_nonresonant_no_dvd
    (m B e f g x y z : Nat) (u v w : Int)
    (hB : 0<B) (hsize : 3*B≤m) (hg : g=0)
    (hu : u%2=1) (hv : v%2=1) (hw : w%2=1)
    (hxy : (e+x)%m ≠ (f+y)%m)
    (hxz : (e+x)%m ≠ (g+z)%m)
    (hyz : (f+y)%m ≠ (g+z)%m)
    (hmass : ∀ h<m, mass (rotate m h [(u*2^x,e),(v*2^y,f),(w*2^z,g)])<2^B) :
    ¬ denominator m ∣ value [(u*2^x,e),(v*2^y,f),(w*2^z,g)] := by
  intro hd
  subst g
  obtain ⟨h,hh,hhB,he⟩ := exists_good_shift [e,f] m B hB (by simpa using hsize)
  have hm : 0<m := by omega
  have hzero := rotation_zero_of_gap m B h [(u*2^x,e),(v*2^y,f),(w*2^z,0)] (by omega) (by
    intro t ht
    simp [rotate,rotateTerm] at ht
    rcases ht with rfl|rfl|rfl
    · exact he e (by simp)
    · exact he f (by simp)
    · simpa [Nat.mod_eq_of_lt hh] using hhB) (hmass h hh) hd
  have hnon := three_odd_distinct (u*(-3)^((e+h)/m)) (v*(-3)^((f+h)/m)) (w*(-3)^((0+h)/m))
    ((e+h)%m+x) ((f+h)%m+y) ((0+h)%m+z)
    (odd_mul_neg_three_pow _ _ hu) (odd_mul_neg_three_pow _ _ hv) (odd_mul_neg_three_pow _ _ hw)
    (adjusted_distinct m h e f x y hm hxy)
    (adjusted_distinct m h e 0 x z hm hxz)
    (adjusted_distinct m h f 0 y z hm hyz)
  apply hnon
  simp only [rotate,List.map_cons,List.map_nil,rotateTerm,value,Int.add_zero] at hzero
  simp only [Int.pow_add]
  grind

/-- Uniform rotation mass bound with an exact integer ceiling. -/
theorem mass_rotate_le (m h E : Nat) (ts : List Term)
    (hm : 0<m) (hh : h<m) (he : ∀ t ∈ ts, t.2≤E) :
    mass (rotate m h ts) ≤ mass ts * 2^(2*((E+m-1)/m)) := by
  induction ts with
  | nil => simp [rotate,mass]
  | cons t ts ih =>
    rcases t with ⟨c,e⟩
    have he0 := he (c,e) (by simp)
    have he1 : ∀ t ∈ ts, t.2≤E := fun t ht => he t (by simp [ht])
    have hq : (e+h)/m ≤ (E+m-1)/m := Nat.div_le_div_right (by omega)
    have hp : (3:Nat)^((e+h)/m) ≤ 2^(2*((E+m-1)/m)) := by
      rw [Nat.pow_mul]
      exact Nat.le_trans (Nat.pow_le_pow_left (by decide : 3≤2^2) _) (Nat.pow_le_pow_right (by decide) hq)
    simp only [rotate,List.map_cons,rotateTerm,mass,Int.natAbs_mul,Int.natAbs_pow] at *
    rw [Nat.add_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ hp) (ih he1)

theorem mass_rotate_lt (m h E H : Nat) (ts : List Term)
    (hm : 0<m) (hh : h<m) (he : ∀ t ∈ ts, t.2≤E) (hH : mass ts<2^H) :
    mass (rotate m h ts) < 2^(H+2*((E+m-1)/m)) := by
  rw [Nat.pow_add]
  exact Nat.lt_of_le_of_lt (mass_rotate_le m h E ts hm hh he)
    (Nat.mul_lt_mul_of_pos_right hH (Nat.two_pow_pos _))

/-- Executable size criterion: a large enough denominator exponent forces a
collision among the three adjusted exponents, for any signed coefficients
with their exact binary valuations factored out. -/
theorem three_resonance_or_small
    (m E H e f x y z : Nat) (u v w : Int)
    (he : e≤E) (hf : f≤E)
    (hu : u%2=1) (hv : v%2=1) (hw : w%2=1)
    (hH : mass [(u*2^x,e),(v*2^y,f),(w*2^z,0)]<2^H)
    (hd : denominator m ∣ value [(u*2^x,e),(v*2^y,f),(w*2^z,0)]) :
    m<3*(H+2*((E+m-1)/m)) ∨
    (e+x)%m=(f+y)%m ∨ (e+x)%m=z%m ∨ (f+y)%m=z%m := by
  by_cases hB : 0 < H+2*((E+m-1)/m)
  · by_cases hsize : m<3*(H+2*((E+m-1)/m))
    · exact Or.inl hsize
    · right
      by_cases hxy : (e+x)%m=(f+y)%m
      · exact Or.inl hxy
      by_cases hxz : (e+x)%m=z%m
      · exact Or.inr (Or.inl hxz)
      by_cases hyz : (f+y)%m=z%m
      · exact Or.inr (Or.inr hyz)
      exfalso
      have hn := three_nonresonant_no_dvd m (H+2*((E+m-1)/m)) e f 0 x y z u v w hB (by omega) rfl hu hv hw
        hxy (by simpa using hxz) (by simpa using hyz) (by
          intro h hh
          exact mass_rotate_lt m h E H _ (by omega) hh (by
            intro t ht
            simp at ht
            rcases ht with rfl|rfl|rfl
            · exact he
            · exact hf
            · simp) hH)
      exact hn hd
  · have hHz : H=0 := by omega
    rw [hHz] at hH
    simp only [mass,Nat.pow_zero,Int.natAbs_mul,Int.natAbs_pow] at hH
    have hu0 : u≠0 := by omega
    have hp : 0<u.natAbs*2^x := Nat.mul_pos (Int.natAbs_pos.mpr hu0) (Nat.two_pow_pos _)
    have heq : (2:Int).natAbs=2 := rfl
    rw [heq] at hH
    omega

theorem three_power_dvd_term (m h a : Nat) (t : Term) (ha : a≤t.2) :
    (3:Int)^(a/m) ∣ (rotateTerm m h t).1*2^(rotateTerm m h t).2 := by
  rcases t with ⟨c,e⟩
  have hq : a/m≤(e+h)/m := Nat.div_le_div_right (by omega)
  have hp : (3:Int)^(a/m) ∣ (-3:Int)^((e+h)/m) := by
    apply Int.natAbs_dvd_natAbs.mp
    simp only [Int.natAbs_pow]
    exact Nat.pow_dvd_pow 3 hq
  exact Int.dvd_mul_of_dvd_left (Int.dvd_mul_of_dvd_right hp)

/-- A three-term sparse expression divisible by 2^m+3 has a small m,
    or its constant coefficient contains a large power of three. -/
theorem three_constant_dvd_or_small
    (m E H a e f : Nat) (c d C : Int)
    (hae : a≤e) (haf : a≤f) (he : e≤E) (hf : f≤E)
    (hH : mass [(c,e),(d,f),(C,0)]<2^H)
    (hd : denominator m ∣ value [(c,e),(d,f),(C,0)]) :
    m<3*(H+2*((E+m-1)/m)) ∨ (3:Int)^(a/m) ∣ C := by
  let B := H+2*((E+m-1)/m)
  change m<3*B ∨ _
  by_cases hB : 0<B
  · by_cases hsize : m<3*B
    · exact Or.inl hsize
    · right
      obtain ⟨h,hh,hhB,hex⟩ := exists_good_shift [e,f] m B hB (by simpa using (show 3*B≤m by omega))
      have hm : 0<m := by omega
      have hzero := rotation_zero_of_gap m B h [(c,e),(d,f),(C,0)] (by omega) (by
        intro t ht
        simp [rotate,rotateTerm] at ht
        rcases ht with rfl|rfl|rfl
        · exact hex e (by simp)
        · exact hex f (by simp)
        · simpa [Nat.mod_eq_of_lt hh] using hhB)
        (mass_rotate_lt m h E H _ hm hh (by
          intro t ht
          simp at ht
          rcases ht with rfl|rfl|rfl
          · exact he
          · exact hf
          · simp) hH) hd
      have h1 := three_power_dvd_term m h a (c,e) hae
      have h2 := three_power_dvd_term m h a (d,f) haf
      have h12 := Int.dvd_add h1 h2
      simp only [rotate,List.map_cons,List.map_nil,rotateTerm,value,Int.add_zero] at hzero
      simp only [rotateTerm] at h12
      simp [Nat.div_eq_of_lt hh, Nat.mod_eq_of_lt hh] at hzero
      have heq : C*2^h = -((c*(-3)^((e+h)/m))*2^((e+h)%m)+(d*(-3)^((f+h)/m))*2^((f+h)%m)) := by omega
      have hC : (3:Int)^(a/m) ∣ C*2^h := by
        rw [heq,Int.dvd_neg]
        exact h12
      apply Int.natAbs_dvd_natAbs.mp
      have hNat := Int.natAbs_dvd_natAbs.mpr hC
      simp only [Int.natAbs_pow,Int.natAbs_mul] at hNat ⊢
      exact (((by decide : (3:Nat).Coprime 2).pow_left (a/m)).pow_right h).dvd_of_dvd_mul_right hNat
  · right
    have hHz : H=0 := by dsimp [B] at hB; omega
    rw [hHz] at hH
    simp only [mass,Nat.pow_zero] at hH
    have hC : C=0 := Int.natAbs_eq_zero.mp (by omega)
    simp [hC]

#print axioms three_constant_dvd_or_small
#print axioms mass_rotate_lt
#print axioms three_resonance_or_small
#print axioms three_nonresonant_no_dvd
end NeedleRotation
