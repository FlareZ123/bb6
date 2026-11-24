import Cap
namespace Cap

theorem c_strict {i j : Nat} (h : i<j) : c i<c j := by
  have hp := Nat.pow_lt_pow_right (by decide : 1<2) h
  have hi := c_add i
  have hj := c_add j
  omega

theorem c_mono {i j : Nat} (h : i≤j) : c i≤c j := by
  by_cases he : i=j
  · subst j; exact Nat.le_refl _
  · exact Nat.le_of_lt (c_strict (by omega))

theorem pow_nonzero_mod3 (i : Nat) : 2^i%3=1 ∨ 2^i%3=2 := by
  induction i with
  | zero => decide
  | succ i ih =>
    rw [Nat.pow_succ, Nat.mul_mod]
    rcases ih with h|h <;> rw [h] <;> decide

theorem c_nonzero_mod3 (i : Nat) : (c i+4)%3≠0 := by
  rw [c_add,Nat.mul_mod]
  rcases pow_nonzero_mod3 i with h|h <;> rw [h] <;> decide

inductive Edge : Nat → Nat → Prop where
  | one : Edge 1 5
  | regular (i r : Nat) (h : r≤c i) : Edge (lo i+r) (3*r+c i+7)
  | special (i : Nat) : Edge (lo i+c i+2) (2*c i+8)

theorem edge_iff {x y : Nat} : Edge x y ↔ f x=some y := by
  constructor
  · intro h
    cases h with
    | one => decide
    | regular i r hr => rw [f_band]; simp [hr]
    | special i =>
      rw [show lo i+c i+2=lo i+(c i+2) by omega,f_band]
      simp only [show ¬ c i+2≤c i by omega,ite_false,show c i+2≠c i+1 by omega,ite_true]
  · intro h
    by_cases h0 : x=0
    · subst x; simp [f] at h
    by_cases h1 : x=1
    · subst x
      have he : 5=y := by simpa [f] using h
      rw [←he]; exact Edge.one
    obtain ⟨i,hi,hj⟩ := band_exists x (by omega)
    let r := x-lo i
    have hr : x=lo i+r := by dsimp [r]; omega
    rw [lo_step] at hj
    have hbound : r≤c i+2 := by omega
    rw [hr,f_band] at h
    rw [hr]
    by_cases hc : r≤c i
    · simp [hc] at h
      rw [←h]; exact Edge.regular i r hc
    · by_cases he : r=c i+1
      · rw [if_neg hc,if_pos he] at h
        contradiction
      · have he2 : r=c i+2 := by omega
        rw [if_neg hc,if_neg he,if_pos he2] at h
        have hy : y=2*c i+8 := Option.some.inj h.symm
        rw [he2,hy,←Nat.add_assoc]; exact Edge.special i

theorem edge_grows {x y : Nat} (h : Edge x y) : x<y := by
  cases h with
  | one => decide
  | regular i r hr => have := lo_c i; omega
  | special i => have := lo_c i; omega

theorem edge_regular_injective (i j r s : Nat) (hr : r≤c i) (hs : s≤c j)
    (he : 3*r+c i+7=3*s+c j+7) : i=j ∧ r=s := by
  have ord : ∀ {a b u v : Nat}, a<b → u≤c a → v≤c b →
      3*u+c a+7≠3*v+c b+7 := by
    intro a b u v hab hu hv heq
    by_cases hj : b=a+1
    · rw [hj,c_succ] at heq
      have hm : (c a+4)%3=0 := by omega
      exact c_nonzero_mod3 a hm
    · have hab2 : a+2≤b := by omega
      have hm := c_mono hab2
      rw [show a+2=(a+1)+1 by omega,c_succ,c_succ] at hm
      omega
  by_cases hij : i=j
  · subst j; exact ⟨rfl,by omega⟩
  · exfalso
    rcases Nat.lt_or_gt_of_ne hij with h|h
    · exact ord h hr hs he
    · exact ord h hs hr he.symm

theorem special_regular_disjoint (i j r : Nat) (hr : r≤c j) :
    2*c i+8≠3*r+c j+7 := by
  intro he
  by_cases hij : i=j
  · subst j
    have hm : (c i+4)%3=0 := by omega
    exact c_nonzero_mod3 i hm
  rcases Nat.lt_or_gt_of_ne hij with h|h
  · have hm := c_mono (show i+1≤j by omega)
    rw [c_succ] at hm
    omega
  · have hm := c_mono (show j+1≤i by omega)
    rw [c_succ] at hm
    omega

theorem edge_inverse_unique {x z y : Nat} (h : Edge x y) (g : Edge z y) : x=z := by
  cases h with
  | one =>
    cases g with
    | one => rfl
  | regular i r hr =>
    generalize he : 3*r+c i+7=y at g
    cases g with
    | one => omega
    | regular j s hs =>
      obtain ⟨hi,hrr⟩ := edge_regular_injective i j r s hr hs he
      subst j; subst s; rfl
    | special j => exact False.elim (special_regular_disjoint j i r hr he.symm)
  | special i =>
    generalize he : 2*c i+8=y at g
    cases g with
    | one => omega
    | regular j s hs => exact False.elim (special_regular_disjoint i j s hs he)
    | special j =>
      have hi : i=j := by
        by_cases hij : i=j
        · exact hij
        · rcases Nat.lt_or_gt_of_ne hij with h|h
          · have := c_strict h; omega
          · have := c_strict h; omega
      subst j; rfl

theorem f_injective {x z y : Nat} (h : f x=some y) (g : f z=some y) : x=z :=
  edge_inverse_unique (edge_iff.mpr h) (edge_iff.mpr g)

theorem edge_no_multiple3 {x y : Nat} (h : Edge x y) : y%3≠0 := by
  cases h with
  | one => decide
  | regular i r hr =>
    intro hm
    exact c_nonzero_mod3 i (by omega)
  | special i =>
    intro hm
    exact c_nonzero_mod3 i (by omega)

theorem f_none_iff {x : Nat} (hx : 2≤x) : f x=none ↔ ∃ i, x=halt i := by
  constructor
  · intro h
    obtain ⟨i,hi,hj⟩ := band_exists x hx
    let r := x-lo i
    have hr : x=lo i+r := by dsimp [r]; omega
    rw [lo_step] at hj
    have hbound : r≤c i+2 := by omega
    rw [hr,f_band] at h
    by_cases hc : r≤c i
    · simp [hc] at h
    · by_cases he : r=c i+1
      · exact ⟨i,by rw [hr,he]; rfl⟩
      · have he2 : r=c i+2 := by omega
        rw [if_neg hc,if_neg he,if_pos he2] at h
        contradiction
  · rintro ⟨i,rfl⟩
    unfold halt
    rw [show lo i+c i+1=lo i+(c i+1) by omega,f_band]
    simp

theorem halt_formula (i : Nat) : halt i+i+6=10*2^i := by
  unfold halt
  have := lo_add i
  have := c_add i
  omega

theorem halt_root_ne (i : Nat) : halt i≠2 := by
  unfold halt
  have := lo_ge i
  omega

theorem no_parent_if_mod3 (i : Nat) (h : halt i%3=0) : ∀ x, f x≠some (halt i) := by
  intro x hF
  exact edge_no_multiple3 (edge_iff.mpr hF) h

-- At most two adjacent band candidates, determined by one bit length.
theorem regular_log_bounds (i r : Nat) (hr : r≤c i) :
    i≤Nat.log2 ((3*r+c i+7)/5) ∧ Nat.log2 ((3*r+c i+7)/5)≤i+1 := by
  have hi := c_add i
  have hp : 0<2^i := Nat.two_pow_pos i
  have hlow : 2^i≤(3*r+c i+7)/5 := by omega
  have hhigh : (3*r+c i+7)/5<2^(i+2) := by
    rw [Nat.pow_add]
    simp
    omega
  have hn : (3*r+c i+7)/5≠0 := by omega
  exact ⟨(Nat.le_log2 hn).mpr hlow,by have := (Nat.log2_lt hn).mpr hhigh; omega⟩

theorem special_log (i : Nat) : Nat.log2 ((2*c i+8)/5)=i+1 := by
  have h := c_add i
  have he : (2*c i+8)/5=2^(i+1) := by rw [Nat.pow_succ]; omega
  rw [he,Nat.log2_two_pow]

def predAt (i y : Nat) : Option Nat :=
  if y=2*c i+8 then some (lo i+c i+2)
  else if c i+7≤y ∧ (y-(c i+7))%3=0 ∧ (y-(c i+7))/3≤c i then
    some (lo i+(y-(c i+7))/3)
  else none

theorem predAt_sound {i y x : Nat} (h : predAt i y=some x) : Edge x y := by
  unfold predAt at h
  by_cases he : y=2*c i+8
  · rw [if_pos he] at h
    cases h; rw [he]; exact Edge.special i
  · rw [if_neg he] at h
    split at h
    next hh =>
      cases h
      have hy : y=3*((y-(c i+7))/3)+c i+7 := by omega
      -- rewrite only the target of the edge; keep the source expression
      have hed := Edge.regular i ((y-(c i+7))/3) hh.2.2
      rw [←hy] at hed
      exact hed
    next hh => contradiction

theorem predAt_regular (i r : Nat) (h : r≤c i) :
    predAt i (3*r+c i+7)=some (lo i+r) := by
  unfold predAt
  rw [if_neg (Ne.symm (special_regular_disjoint i i r h))]
  have he : 3*r+c i+7-(c i+7)=3*r := by omega
  rw [he]
  simp [show c i+7≤3*r+c i+7 by omega,h]

theorem predAt_special (i : Nat) : predAt i (2*c i+8)=some (lo i+c i+2) := by simp [predAt]

def predecessor (y : Nat) : Option Nat :=
  if y=5 then some 1 else
    let j := Nat.log2 (y/5)
    match predAt j y with
    | some x => some x
    | none => predAt (j-1) y

theorem predecessor_sound {x y : Nat} (h : predecessor y=some x) : Edge x y := by
  unfold predecessor at h
  split at h
  next he => cases h; rw [he]; exact Edge.one
  next he =>
    dsimp at h
    split at h
    next z hz => cases h; exact predAt_sound hz
    next hz => exact predAt_sound h

theorem predecessor_complete {x y : Nat} (h : Edge x y) : predecessor y=some x := by
  have aux : ∀ {i y x : Nat}, y≠5 → predAt i y=some x →
      i≤Nat.log2 (y/5) → Nat.log2 (y/5)≤i+1 → predecessor y=some x := by
    intro i y x hy hp hlo hhi
    unfold predecessor
    rw [if_neg hy]
    dsimp
    by_cases he : Nat.log2 (y/5)=i
    · rw [he,hp]
    · have he2 : Nat.log2 (y/5)=i+1 := by omega
      rw [he2]
      cases hnext : predAt (i+1) y with
      | none => simpa using hp
      | some z =>
        have heq := edge_inverse_unique (predAt_sound hnext) (predAt_sound hp)
        rw [heq]
  cases h with
  | one => decide
  | regular i r hr =>
    obtain ⟨hl,hh⟩ := regular_log_bounds i r hr
    exact aux (by omega) (predAt_regular i r hr) hl hh
  | special i =>
    exact aux (by omega) (predAt_special i) (by rw [special_log]; omega) (by rw [special_log]; exact Nat.le_refl _)

theorem predecessor_iff {x y : Nat} : predecessor y=some x ↔ f x=some y :=
  ⟨fun h=>edge_iff.mp (predecessor_sound h),fun h=>predecessor_complete (edge_iff.mpr h)⟩

#print axioms eval_odd
#print axioms f_band
#print axioms f_injective
#print axioms f_none_iff
#print axioms predecessor_iff
end Cap
