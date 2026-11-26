import DyadicSeam
namespace DyadicSeam
set_option maxHeartbeats 0

theorem numerator_mod {q p0 J p : Nat} (hs : Shape q p0 J p) :
    p%2^(q-J)=p0%2^(q-J) := by
  by_cases hJ : J<q
  · by_cases hzero : J=0
    · rw [hs.1 hzero]
    · obtain ⟨d,_,he⟩ := hs.2.1 (by omega) hJ
      rw [he]
      simp [Nat.add_mod,Nat.mul_mod]
  · have e : q-J=0 := by omega
    simp [e,Nat.mod_one]

theorem quotient_bound {q : Nat} {s : Node} (hb : Band q s) :
    s.p/2^(q-s.J)<3^s.A := by
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
  simpa [Nat.mul_comm] using hb.2

theorem quotient_unique {q p0 J p r : Nat} (hp : Shape q p0 J p) (hr : Shape q p0 J r)
    (he : p/2^(q-J)=r/2^(q-J)) : p=r := by
  have hm := (numerator_mod hp).trans (numerator_mod hr).symm
  have h1 := Nat.mod_add_div p (2^(q-J))
  have h2 := Nat.mod_add_div r (2^(q-J))
  rw [hm,he] at h1
  omega

def Word (q p0 : Nat) := {p : Node × List (Nat × Nat) // Path q p0 p.1 p.2}

def index (q Amax : Nat) (s : Node) : Nat :=
  (s.J*(Amax+1)+s.A)*3^Amax + s.p/2^(q-s.J)

theorem index_injective {q p0 Amax : Nat} (hq : 0<q) (hp : p0%2=1)
    {s t : Word q p0} (hsJ : 0<s.val.1.J) (htJ : 0<t.val.1.J)
    (hsA : s.val.1.A≤Amax) (htA : t.val.1.A≤Amax)
    (he : index q Amax s.val.1=index q Amax t.val.1) : s=t := by
  have hb {u : Node} {w : List (Nat × Nat)} (h : Path q p0 u w) (hJ : 0<u.J) : Band q u := by
    cases h with
    | nil => simp [root] at hJ
    | cons he _ => exact he.2.2.2.1
  have hbs := quotient_bound (hb s.property hsJ)
  have hbt := quotient_bound (hb t.property htJ)
  have hslt : s.val.1.p/2^(q-s.val.1.J)<3^Amax := Nat.lt_of_lt_of_le hbs (Nat.pow_le_pow_right (by decide) hsA)
  have htlt : t.val.1.p/2^(q-t.val.1.J)<3^Amax := Nat.lt_of_lt_of_le hbt (Nat.pow_le_pow_right (by decide) htA)
  have hquot := congrArg (fun n : Nat => n/3^Amax) he
  have hrem := congrArg (fun n : Nat => n%3^Amax) he
  simp [index,Nat.add_mod,Nat.mul_mod,Nat.mod_eq_of_lt hslt,Nat.mod_eq_of_lt htlt] at hrem
  rw [show index q Amax s.val.1=s.val.1.p/2^(q-s.val.1.J)+3^Amax*(s.val.1.J*(Amax+1)+s.val.1.A) by unfold index; ac_rfl,
      show index q Amax t.val.1=t.val.1.p/2^(q-t.val.1.J)+3^Amax*(t.val.1.J*(Amax+1)+t.val.1.A) by unfold index; ac_rfl] at hquot
  rw [Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide) : 0<3^Amax),Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide) : 0<3^Amax),Nat.div_eq_of_lt hslt,Nat.div_eq_of_lt htlt] at hquot
  simp only [Nat.zero_add] at hquot
  have hJ := congrArg (fun n : Nat => n/(Amax+1)) hquot
  have hA := congrArg (fun n : Nat => n%(Amax+1)) hquot
  rw [Nat.mul_comm s.val.1.J, Nat.mul_comm t.val.1.J,Nat.add_comm ( (Amax+1)*s.val.1.J),Nat.add_comm ((Amax+1)*t.val.1.J)] at hJ
  rw [Nat.add_mul_div_left _ _ (by omega : 0<Amax+1),Nat.add_mul_div_left _ _ (by omega : 0<Amax+1),Nat.div_eq_of_lt (by omega : s.val.1.A<Amax+1),Nat.div_eq_of_lt (by omega : t.val.1.A<Amax+1)] at hJ
  simp only [Nat.zero_add] at hJ
  simp [Nat.add_mod,Nat.mul_mod,Nat.mod_eq_of_lt (by omega : s.val.1.A<Amax+1),Nat.mod_eq_of_lt (by omega : t.val.1.A<Amax+1)] at hA
  rw [hJ] at hrem
  have hpEq := quotient_unique (by rw [←hJ]; exact path_shape hq hp s.property) (path_shape hq hp t.property) hrem
  have hnode : s.val.1=t.val.1 := by cases hs : s.val.1; cases ht : t.val.1; simp_all
  apply Subtype.ext
  apply Prod.ext hnode
  exact path_unique hq hp (hnode ▸ s.property) t.property

theorem index_bound {q Amax Jmax : Nat} {s : Node} (hb : Band q s)
    (hA : s.A≤Amax) (hJ : s.J≤Jmax) : index q Amax s<(Jmax+1)*(Amax+1)*3^Amax := by
  have hq := quotient_bound hb
  have hlt := Nat.lt_of_lt_of_le hq (Nat.pow_le_pow_right (by decide : 0<3) hA)
  have h1 : s.J*(Amax+1)+s.A < (Jmax+1)*(Amax+1) := by
    have hm := Nat.mul_le_mul_right (Amax+1) hJ
    rw [Nat.add_mul]
    omega
  have h2 := Nat.mul_le_mul_right (3^Amax) (show s.J*(Amax+1)+s.A+1≤(Jmax+1)*(Amax+1) by omega)
  rw [Nat.add_mul] at h2
  unfold index
  omega

theorem bounded_word_count {q p0 Amax Jmax : Nat} (hq : 0<q) (hp : p0%2=1)
    (xs : List (Word q p0)) (hn : xs.Nodup)
    (hb : ∀ x∈xs, 0<x.val.1.J ∧ x.val.1.J≤Jmax ∧ x.val.1.A≤Amax) :
    xs.length≤(Jmax+1)*(Amax+1)*3^Amax := by
  let f : Word q p0 → Nat := fun x=>index q Amax x.val.1
  have hm : (xs.map f).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem _ hn
    intro x y hx hy hne he
    exact hne (index_injective hq hp (hb x hx).1 (hb y hy).1 (hb x hx).2.2 (hb y hy).2.2 he)
  have hsub : xs.map f ⊆ List.range ((Jmax+1)*(Amax+1)*3^Amax) := by
    intro i hi
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hi
    apply List.mem_range.mpr
    have hb' := hb x hx
    have path_band {u : Node} {w : List (Nat × Nat)} (h : Path q p0 u w) (hJ : 0<u.J) : Band q u := by
      cases h with
      | nil => simp [root] at hJ
      | cons he _ => exact he.2.2.2.1
    have hband := path_band x.property hb'.1
    exact index_bound hband hb'.2.2 hb'.2.1
  have hh := hm.length_le_of_subset hsub
  simpa using hh

#print axioms numerator_mod
#print axioms index_injective
#print axioms bounded_word_count
end DyadicSeam
