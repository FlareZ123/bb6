import CapSieveGraph
namespace CapSieve

def Band (j x : Nat) : Prop := L j≤x ∧ x<L (j+1)

theorem l_succ (j : Nat) : L (j+1)=L j+P j-1 := by
  have h:=l_add j
  have h' := l_add (j+1)
  rw [p_succ] at h'
  omega

theorem band_bounds {j x : Nat} (h : Band j x) :
    L j≤x ∧ x+j+5≤2*P j := by
  have h' := l_add (j+1)
  rw [p_succ] at h'
  unfold Band at h
  omega

theorem l_mono {j k : Nat} (h : j≤k) : L j≤L k := by
  induction k with
  | zero =>
    have he : j=0 := by omega
    subst j; exact Nat.le_refl _
  | succ k ih =>
    by_cases he : j=k+1
    · simp [he]
    · have hh:=ih (by omega)
      have hp:=p_ge k
      rw [l_succ]; omega

theorem band_unique {j k x : Nat} (h : Band j x) (h' : Band k x) : j=k := by
  unfold Band at *
  by_cases e : j=k
  · exact e
  · by_cases he : j<k
    · have hm := l_mono (show j+1≤k by omega); omega
    · have hm := l_mono (show k+1≤j by omega); omega

theorem regular_band (k r : Nat) (hr : r+4≤P k) : Band k (L k+r) := by
  unfold Band
  have hp:=p_ge k
  rw [l_succ]
  omega

theorem special_band (k : Nat) : Band k (L k+(P k-2)) := by
  unfold Band
  have hp:=p_ge k
  rw [l_succ]
  omega

theorem p_ge_large {j : Nat} (h : 6≤j) : 4*j+30≤P j := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases he : j<6
    · have : j=5 := by omega
      subst j; decide
    · have hh := ih (by omega)
      rw [p_succ]; omega

theorem p_ge_mid {j : Nat} (h : 4≤j) : 2*j+12≤P j := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases he : j<4
    · have : j=3 := by omega
      subst j; decide
    · have hh := ih (by omega)
      rw [p_succ]; omega

theorem regular_target_band {j k r : Nat} (hj : Band j (3*r+P k+3)) (hr : r+4≤P k) :
    k≤j ∧ j≤k+2 := by
  have hh:=band_bounds hj
  have hk:=l_add j
  constructor
  · by_cases he : k≤j
    · exact he
    · have hm:=p_mono (show j+1≤k by omega)
      rw [p_succ] at hm; omega
  · by_cases he : j≤k+2
    · exact he
    · have hm:=l_mono (show k+3≤j by omega)
      have hl:=l_add (k+3)
      have hp : P (k+3)=8*P k := by rw [show k+3=(k+2)+1 by omega,p_succ,show k+2=(k+1)+1 by omega,p_succ,p_succ]; omega
      rw [hp] at hl
      have := p_ge k
      omega

theorem special_target_band (k : Nat) : Band (k+1) (2*P k) := by
  unfold Band
  have h:=l_add (k+1)
  have h':=l_add (k+2)
  rw [p_succ] at h
  rw [show k+2=(k+1)+1 by omega,p_succ,p_succ] at h'
  have := p_ge k
  omega

def RegFrom (k x y : Nat) : Prop := ∃ r, r+4≤P k ∧ x=L k+r ∧ y=3*r+P k+3

theorem regFrom_iff {k y : Nat} : (∃ x, RegFrom k x y) ↔
    P k+3≤y ∧ y+9≤4*P k ∧ y%3=P k%3 := by
  constructor
  · rintro ⟨x,r,hr,_,hy⟩
    omega
  · rintro ⟨hl,hh,hm⟩
    let r := (y-(P k+3))/3
    have he : y=3*r+P k+3 := by dsimp [r]; omega
    exact ⟨L k+r,r,by omega,rfl,he⟩

theorem regFrom_arc {k x y : Nat} (h : RegFrom k x y) : Arc x y := by
  obtain ⟨r,hr,rfl,rfl⟩:=h
  exact .regular k r hr

/-- All inverse possibilities for every band j≥6, with no depth guard. -/
theorem large_band_arc {j y x : Nat} (hj : 6≤j) (hb : Band j y) : Arc x y ↔
    RegFrom j x y ∨ RegFrom (j-1) x y ∨ RegFrom (j-2) x y ∨
      (y=P j ∧ x=L (j-1)+(P (j-1)-2)) := by
  constructor
  · intro h
    cases h with
    | one =>
      have hh:=band_bounds hb
      have hl:=l_add j
      have hp:=p_ge_large hj
      omega
    | regular k r hr =>
      have hk:=regular_target_band hb hr
      by_cases he : k=j
      · subst k; exact Or.inl ⟨r,hr,rfl,rfl⟩
      · by_cases he' : k=j-1
        · subst k; exact Or.inr (Or.inl ⟨r,hr,rfl,rfl⟩)
        · have he'' : k=j-2 := by omega
          subst k; exact Or.inr (Or.inr (Or.inl ⟨r,hr,rfl,rfl⟩))
    | special k =>
      have he:=band_unique hb (special_target_band k)
      have hk : k=j-1 := by omega
      subst k
      have hp : P j=2*P (j-1) := by exact (congrArg P (show j=j-1+1 by omega)).trans (p_succ (j-1))
      exact Or.inr (Or.inr (Or.inr ⟨hp.symm,rfl⟩))
  · rintro (h|h|h|⟨hy,hx⟩)
    · exact regFrom_arc h
    · exact regFrom_arc h
    · exact regFrom_arc h
    · rw [hy,hx,show P j=2*P (j-1) by exact (congrArg P (show j=j-1+1 by omega)).trans (p_succ (j-1))]
      exact .special (j-1)

/-- Exactly the two missing boundary values, in addition to the multiples of 3. -/
theorem large_band_no_parent {j y : Nat} (hj : 6≤j) (hb : Band j y) :
    (¬ ∃ x, Arc x y) ↔ y%3=0 ∨ y+3=P j ∨ y+6=P j := by
  have hP:=p_ge_large hj
  have hP1:=p_ge_mid (j:=j-1) (by omega)
  have hP2:=p_ge_mid (j:=j-2) (by omega)
  have h1 : P j=2*P (j-1) := by exact (congrArg P (show j=j-1+1 by omega)).trans (p_succ (j-1))
  have h2 : P (j-1)=2*P (j-2) := by exact (congrArg P (show j-1=j-2+1 by omega)).trans (p_succ (j-2))
  have hh:=band_bounds hb
  have hl:=l_add j
  have hm1 := p_adjacent (j-1)
  rw [show j-1+1=j by omega] at hm1
  have hm2 : P (j-2)%3=P j%3 := by
    rw [h1,h2,show 2*(2*P (j-2))=4*P (j-2) by omega,Nat.mul_mod]
    rcases p_nonzero (j-2) with h|h <;> rw [h] <;> decide
  have hR1 : (∃ x, RegFrom (j-1) x y) ↔ y%3=P (j-1)%3 := by
    rw [regFrom_iff]; omega
  have hR0 : (∃ x, RegFrom j x y) ↔ P j+3≤y ∧ y%3=P j%3 := by
    rw [regFrom_iff]; omega
  have hR2 : (∃ x, RegFrom (j-2) x y) ↔ y+9≤P j ∧ y%3=P j%3 := by
    rw [regFrom_iff]; omega
  have he : (∃ x, Arc x y) ↔ (P j+3≤y ∧ y%3=P j%3) ∨ y%3=P (j-1)%3 ∨ (y+9≤P j ∧ y%3=P j%3) ∨ y=P j := by
    simp only [large_band_arc hj hb,exists_or,hR0,hR1,hR2,exists_and_left,exists_eq, and_true]
  rw [he]
  have hp := p_nonzero j
  have hp' := p_nonzero (j-1)
  omega

#print axioms large_band_arc
#print axioms large_band_no_parent
end CapSieve
