import HaltCylinders

namespace BB6.Agent26.HaltCylinders
open CryptidBoundary

private theorem unit_digit (A v : Nat) (hA : A%3≠0) :
    ∃ t, t<3 ∧ (v+A*t)%3=0 := by
  have h0 : (v+A*0)%3=v%3 := by simp
  have h1 : (v+A*1)%3=(v%3+A%3)%3 := by rw [Nat.mul_one,Nat.add_mod]
  have h2 : (v+A*2)%3=(v%3+A%3*2)%3 := by
    rw [Nat.add_mod,Nat.mul_mod A 2 3]
    omega
  by_cases ha : A%3=1 <;> by_cases hv : v%3=0 <;> by_cases hv' : v%3=1
  all_goals first | exact ⟨0,by decide,by omega⟩ | exact ⟨1,by decide,by omega⟩ | exact ⟨2,by decide,by omega⟩ | omega

/-- Hensel lifting of a unit inverse, with no integer subtraction. -/
theorem unit_inverse (A d : Nat) (hA : A%3≠0) :
    ∃ u v : Nat, A*u=1+3^d*v := by
  induction d with
  | zero => exact ⟨1,A-1,by simp; omega⟩
  | succ d ih =>
    obtain ⟨u,v,huv⟩ := ih
    obtain ⟨t,ht,hdiv⟩ := unit_digit A v hA
    have h := Nat.mod_add_div (v+A*t) 3
    rw [hdiv,Nat.zero_add] at h
    refine ⟨u+3^d*t,(v+A*t)/3,?_⟩
    rw [Nat.mul_add,huv,show A*(3^d*t)=3^d*(A*t) by ac_rfl, Nat.add_assoc,←Nat.mul_add,Nat.pow_succ]
    calc
      _ = 1+3^d*(3*((v+A*t)/3)) := by rw [h]
      _ = _ := by ac_rfl

/-- Every progression with ternary-unit stride intersects every ternary
    congruence class. A whole subprogression lies in that class. -/
theorem unit_preimage (d A m c : Nat) (hA : A%3≠0) :
    ∃ p t : Nat, m+A*p=c+3^d*t := by
  obtain ⟨u,v,huv⟩ := unit_inverse A d hA
  let P := 3^d
  let a := c+P*m-m
  have hp : 1≤P := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.pow_pos (by decide)))
  have hm : m ≤ P*m := by simpa using Nat.mul_le_mul_right m hp
  have ha : m+a=c+P*m := by dsimp [a]; omega
  refine ⟨u*a,m+v*a,?_⟩
  change m+A*(u*a)=c+P*(m+v*a)
  rw [←Nat.mul_assoc,huv]
  change m+(1+P*v)*a=c+P*(m+v*a)
  simp only [Nat.add_mul,Nat.one_mul,Nat.mul_add,Nat.mul_assoc,←Nat.add_assoc,ha]

theorem factor_three (M : Nat) (hM : 0<M) :
    ∃ s u : Nat, M=3^s*u ∧ u%3≠0 := by
  induction M using Nat.strongRecOn with
  | ind M ih =>
    by_cases h : M%3=0
    · have hdiv := Nat.mod_add_div M 3
      rw [h,Nat.zero_add] at hdiv
      obtain ⟨s,u,hs,hu⟩ := ih (M/3) (by omega) (by omega)
      refine ⟨s+1,u,?_,hu⟩
      rw [←hdiv,hs,Nat.pow_succ]; ac_rfl
    · exact ⟨0,M,by simp,h⟩

private theorem unit_mul (A B : Nat) (hA : A%3≠0) (hB : B%3≠0) :
    (A*B)%3≠0 := by
  rw [Nat.mul_mod]
  have ha : A%3=1 ∨ A%3=2 := by omega
  have hb : B%3=1 ∨ B%3=2 := by omega
  rcases ha with h|h <;> rcases hb with g|g <;> rw [h,g] <;> decide

private theorem eight_pow_unit (L : Nat) : 8^L%3≠0 := by
  induction L with
  | zero => decide
  | succ L ih => rw [Nat.pow_succ]; exact unit_mul _ _ ih (by decide)

/-- Any source-liftable prefix has a halting extension in the original
    residue modulo every M=3^s*u with s≤L and u a ternary unit. -/
theorem periodic_extension (d c L n m s u : Nat) (v w : List Bool)
    (hm : 2≤m) (hs : s≤L) (hu : u%3≠0)
    (hbase : ∀ z, 2≤z → z%3^d=c%3^d → Halts (sec z []))
    (hlift : ∀ q, Halts (sec (m+8^L*q) w) → Halts (sec (n+3^L*q) v)) :
    ∃ p, ∀ q, Halts (sec (n+3^s*u*(3^(L-s)*(p+3^(d+zeros w)*q))) v) := by
  obtain ⟨r,hr,hh⟩ := suffix_cylinder d c hbase w
  obtain ⟨p,t,ht⟩ := unit_preimage (d+zeros w) (8^L*u) m r (unit_mul _ _ (eight_pow_unit L) hu)
  refine ⟨p,?_⟩
  intro q
  have hpow : 3^s*3^(L-s)=3^L := by rw [←Nat.pow_add,show s+(L-s)=L by omega]
  rw [show 3^s*u*(3^(L-s)*(p+3^(d+zeros w)*q))=3^L*(u*(p+3^(d+zeros w)*q)) by
    calc
      _ = (3^s*3^(L-s))*(u*(p+3^(d+zeros w)*q)) := by ac_rfl
      _ = _ := by rw [hpow]]
  apply hlift
  apply hh _ (by omega)
  rw [←Nat.mul_assoc,Nat.mul_add,←Nat.add_assoc,ht]
  simp [Nat.add_mod,Nat.mul_mod,Nat.mod_eq_of_lt hr]

/-- No forward-periodic safe predicate containing n can survive a prefix
    of length at least the ternary valuation of its modulus. -/
theorem periodic_obstruction (d c L n m s u : Nat) (v w : List Bool)
    (hm : 2≤m) (hs : s≤L) (hu : u%3≠0)
    (hbase : ∀ z, 2≤z → z%3^d=c%3^d → Halts (sec z []))
    (hlift : ∀ q, Halts (sec (m+8^L*q) w) → Halts (sec (n+3^L*q) v))
    (P : Nat → Prop) (hn : P n)
    (hperiod : ∀ x, P x → P (x+3^s*u))
    (hsafe : ∀ x, P x → ¬Halts (sec x v)) : False := by
  obtain ⟨p,hp⟩ := periodic_extension d c L n m s u v w hm hs hu hbase hlift
  have hmult (k : Nat) : P (n+3^s*u*k) := by
    induction k with
    | zero => simpa using hn
    | succ k ih => simpa [Nat.mul_succ,Nat.add_assoc] using hperiod _ ih
  exact hsafe _ (hmult _) (hp 0)

#print axioms unit_inverse
#print axioms factor_three
#print axioms periodic_extension
#print axioms periodic_obstruction
end BB6.Agent26.HaltCylinders
