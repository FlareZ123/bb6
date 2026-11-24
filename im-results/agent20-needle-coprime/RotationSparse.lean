import RotationFar

namespace NeedleRotation

/-- A signed sparse geometric polynomial with its leading coefficient first. -/
def sparse (a : Nat) (c : Int) : Nat → List Term
  | 0 => []
  | n+1 => (c,(n+1)*a)::sparse a (-3*c) n

theorem sparse_length (a n : Nat) (c : Int) : (sparse a c n).length=n := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp [sparse,ih]

theorem sparse_mem (a n : Nat) (c : Int) (t : Term) :
    t ∈ sparse a c n ↔ ∃ l : Nat, 1≤l ∧ l≤n ∧ t=(c*(-3)^(n-l),l*a) := by
  induction n generalizing c with
  | zero => simp [sparse]; omega
  | succ n ih =>
    simp only [sparse,List.mem_cons,ih]
    constructor
    · intro h
      rcases h with ht|⟨l,hl,hln,ht⟩
      · exact ⟨n+1,by omega,by omega,by simpa using ht⟩
      · refine ⟨l,hl,by omega,?_⟩
        rw [ht,show n+1-l=n-l+1 by omega,Int.pow_succ]
        congr 1
        grind
    · rintro ⟨l,hl,hln,ht⟩
      by_cases he : l=n+1
      · left
        rw [ht,he,Nat.sub_self,Int.pow_zero,Int.mul_one]
      · right
        refine ⟨l,hl,by omega,?_⟩
        rw [ht,show n+1-l=n-l+1 by omega,Int.pow_succ]
        congr 1
        grind

theorem sparse_identity (a n : Nat) (c : Int) :
    (2^a+3)*value (sparse a c n)=c*(2^((n+1)*a)-(-3)^n*2^a) := by
  induction n generalizing c with
  | zero => simp [sparse,value]
  | succ n ih =>
    simp only [sparse,value,Int.mul_add]
    rw [ih (-3*c),show (n+1+1)*a=(n+1)*a+a by rw [Nat.add_mul,Nat.one_mul],Int.pow_add,Int.pow_succ]
    grind

theorem mass_le_len_mul (ts : List Term) (M : Nat)
    (hc : ∀ t∈ts,t.1.natAbs≤M) : mass ts≤ts.length*M := by
  induction ts with
  | nil => simp [mass]
  | cons t ts ih =>
    rcases t with ⟨c,e⟩
    have hc0 := hc (c,e) (by simp)
    have hc1 : ∀ t∈ts,t.1.natAbs≤M := fun t ht => hc t (by simp [ht])
    simp only [mass,List.length_cons,Nat.succ_mul]
    have hh := ih hc1
    omega

theorem ceil_mul_ge (a m : Nat) (hm : 0<m) : a≤((a+m-1)/m)*m := by
  have hd := Nat.div_add_mod (a+m-1) m
  have hr := Nat.mod_lt (a+m-1) hm
  rw [Nat.mul_comm m] at hd
  omega

theorem sparse_rotated_mass (a m n h : Nat) (c C : Int)
    (hm : 0<m) (hma : m≤a) (hh : h<m) :
    mass (rotate m h ((C,0)::sparse a c n)) ≤ C.natAbs+n*c.natAbs*3^(n*((a+m-1)/m)) := by
  let k := (a+m-1)/m
  have hk : a≤k*m := ceil_mul_ge a m hm
  have hk1 : 1≤k := by
    by_cases hz : k=0
    · rw [hz,Nat.zero_mul] at hk
      omega
    · exact Nat.one_le_iff_ne_zero.mpr hz
  have hc : ∀ t∈rotate m h (sparse a c n), t.1.natAbs≤c.natAbs*3^(n*k) := by
    intro t ht
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
    obtain ⟨l,hl,hln,hu⟩ := (sparse_mem a n c u).mp hu
    subst u
    simp only [rotateTerm,Int.natAbs_mul,Int.natAbs_pow]
    have hq : (l*a+h)/m≤l*k := by
      apply (Nat.div_le_iff_le_mul hm).mpr
      have hmul := Nat.mul_le_mul_left l hk
      rw [←Nat.mul_assoc] at hmul
      omega
    have hbound : n-l+(l*a+h)/m≤n*k := by
      have hmul : n-l≤(n-l)*k := by
        simpa using Nat.mul_le_mul_left (n-l) hk1
      have heq : n*k=(n-l)*k+l*k := by
        rw [←Nat.add_mul,Nat.sub_add_cancel hln]
      omega
    have hp := Nat.pow_le_pow_right (by decide : 0<(3:Nat)) hbound
    rw [Nat.mul_assoc,←Nat.pow_add]
    exact Nat.mul_le_mul_left _ hp
  have hmass := mass_le_len_mul (rotate m h (sparse a c n)) (c.natAbs*3^(n*k)) hc
  have hlen : (rotate m h (sparse a c n)).length=n := by simp [rotate,sparse_length]
  rw [hlen] at hmass
  simp only [rotate,List.map_cons,rotateTerm,mass,Int.natAbs_mul,Int.natAbs_pow,Nat.zero_add,Nat.div_eq_of_lt hh,Nat.pow_zero,Nat.mul_one]
  change C.natAbs+mass (rotate m h (sparse a c n))≤C.natAbs+n*c.natAbs*3^(n*k)
  rw [Nat.mul_assoc]
  exact Nat.add_le_add_left hmass _

theorem sparse_rotated_term_dvd (a m n h j : Nat) (c : Int) (t : Term)
    (hm : 0<m) (hj : 1≤j) (hja : j*m≤a) (ht : t∈rotate m h (sparse a c n)) :
    (3:Int)^(n+j-1) ∣ t.1*2^t.2 := by
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
  obtain ⟨l,hl,hln,hu⟩ := (sparse_mem a n c u).mp hu
  subst u
  have hq : l*j≤(l*a+h)/m := by
    apply (Nat.le_div_iff_mul_le hm).mpr
    have hh := Nat.mul_le_mul_left l hja
    rw [←Nat.mul_assoc] at hh
    omega
  have hjl : l+j-1≤l*j := by
    have heq : l*j=(l-1)*(j-1)+l+j-1 := by
      have he1 : l=(l-1)+1 := by omega
      have he2 : j=(j-1)+1 := by omega
      calc
        l*j=((l-1)+1)*((j-1)+1) := by rw [←he1,←he2]
        _=(l-1)*(j-1)+l+j-1 := by simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one,Nat.one_mul]; omega
    omega
  have hp : (3:Int)^(n+j-1) ∣ (-3:Int)^(n-l+(l*a+h)/m) := by
    apply Int.natAbs_dvd_natAbs.mp
    simp only [Int.natAbs_pow]
    exact Nat.pow_dvd_pow 3 (by omega)
  simp only [rotateTerm]
  have heq : c*(-3)^(n-l)*(-3)^((l*a+h)/m)*2^((l*a+h)%m) = c*(-3)^(n-l+(l*a+h)/m)*2^((l*a+h)%m) := by
    rw [Int.pow_add]
    grind
  rw [heq]
  exact Int.dvd_mul_of_dvd_left (Int.dvd_mul_of_dvd_right hp)

theorem dvd_value_of_terms (D : Int) (ts : List Term)
    (hd : ∀ t∈ts,D∣t.1*2^t.2) : D∣value ts := by
  induction ts with
  | nil => simp [value]
  | cons t ts ih =>
    rcases t with ⟨c,e⟩
    exact Int.dvd_add (hd (c,e) (by simp)) (ih (fun u hu => hd u (by simp [hu])))

/-- Full signed-geometric low-side rotation lemma, with a stronger 3-adic
conclusion depending on the quotient j=floor(a/m). -/
theorem sparse_constant_dvd
    (a m n B j : Nat) (c C : Int)
    (hm : 0<m) (hB : 0<B) (hj : 1≤j) (hja : j*m≤a)
    (hsize : (n+1)*B≤m)
    (hbound : C.natAbs+n*c.natAbs*3^(n*((a+m-1)/m))<2^B)
    (hd : denominator m∣value ((C,0)::sparse a c n)) :
    (3:Int)^(n+j-1) ∣ C := by
  have hma : m≤a := by
    have hh := Nat.mul_le_mul_right m hj
    simp only [Nat.one_mul] at hh
    omega
  obtain ⟨h,hh,hhB,he⟩ := exists_good_shift ((sparse a c n).map Prod.snd) m B hB (by simpa [sparse_length] using hsize)
  have hmB : B≤m := by
    have hh := Nat.mul_le_mul_right B (show 1≤n+1 by omega)
    omega
  have hmass : mass (rotate m h ((C,0)::sparse a c n))<2^B := Nat.lt_of_le_of_lt (sparse_rotated_mass a m n h c C hm hma hh) hbound
  have hzero := rotation_zero_of_gap m B h ((C,0)::sparse a c n) hmB (by
    intro t ht
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
    rcases List.mem_cons.mp hu with rfl|hu
    · simpa [rotateTerm,Nat.mod_eq_of_lt hh] using hhB
    · exact he u.2 (List.mem_map.mpr ⟨u,hu,rfl⟩)) hmass hd
  have hdiv := dvd_value_of_terms ((3:Int)^(n+j-1)) (rotate m h (sparse a c n)) (fun t ht => sparse_rotated_term_dvd a m n h j c t hm hj hja ht)
  simp only [rotate,List.map_cons,rotateTerm,value,Nat.zero_add,Nat.div_eq_of_lt hh,Nat.mod_eq_of_lt hh,Int.pow_zero,Int.mul_one] at hzero
  have heq : C*2^h= -value (rotate m h (sparse a c n)) := by simpa [rotate] using (show C*2^h= -value ((sparse a c n).map (rotateTerm m h)) by omega)
  have hC : (3:Int)^(n+j-1) ∣ C*2^h := by rw [heq,Int.dvd_neg]; exact hdiv
  apply Int.natAbs_dvd_natAbs.mp
  have hNat := Int.natAbs_dvd_natAbs.mpr hC
  simp only [Int.natAbs_pow,Int.natAbs_mul] at hNat ⊢
  exact (((by decide : (3:Nat).Coprime 2).pow_left (n+j-1)).pow_right h).dvd_of_dvd_mul_right hNat

#print axioms sparse_identity
#print axioms sparse_constant_dvd
end NeedleRotation
