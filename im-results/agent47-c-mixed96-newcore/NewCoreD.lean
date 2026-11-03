import Std
set_option maxHeartbeats 0
set_option maxRecDepth 4000
namespace NewCore

def nextC (t : Nat × Nat × Nat) : Option (Nat × Nat × Nat) :=
  let (a,k,c) := t
  if c = 1 then some (a,k+1,0)
  else if c = 2 then none
  else if c = 3 then some (a,k+2,1)
  else if c = 0 then
    if a = 0 then some (1,0,2*k+2)
    else if a = 1 then
      if k = 0 then some (5,0,1) else some (2,2,2*k-1)
    else some (a-2,1,2*k+1)
  else if a = 0 then
    if k%2 = 0 then some (2*k+2,2,c-3) else some (2*k+3,0,c)
  else some (a-1,k+1,c-1)

def lowD (a k c : Nat) : Prop :=
  (a % 48 = 37 ∧ (a+k+c)%96 = 92) ∨
  (a % 48 = 18 ∧ (k+c)%24 = 11) ∨
  (a % 48 = 42 ∧ (k+c)%24 = 23) ∨
  (a % 48 = 44 ∧ (k+c)%24 = 0)

def highD (a k c : Nat) : Prop :=
  let d := (a + 48 - c%48)%48
  let t := (a+k)%96
  (d=0 ∧ t%24=19) ∨
  (d=15 ∧ t%24=2) ∨
  (d=24 ∧ t%24=7) ∨
  (d=34 ∧ t=89) ∨
  (d=39 ∧ t%24=14) ∨
  (d=41 ∧ (t%24=17 ∨ t%48=43))

def badD (a k c : Nat) : Prop :=
  if c < 2 then lowD a k c else highD a k c

theorem low_transferD (a k : Nat) :
    badD a (k+1) 0 → badD a k 1 := by
  simp only [badD, show (0:Nat)<2 by omega, show (1:Nat)<2 by omega, ↓reduceIte]
  simp only [lowD]
  omega

theorem high_to_low3D (a k : Nat) :
    badD a (k+2) 1 → badD a k 3 := by
  simp only [badD, show (1:Nat)<2 by omega, show ¬((3:Nat)<2) by omega, ↓reduceIte]
  intro h
  simp only [lowD,highD] at *
  rcases h with h | h | h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega)))))

theorem zero_a0D (k : Nat) : ¬badD 1 0 (2*k+2) := by
  have hc : ¬(2*k+2<2) := by omega
  simp only [badD,hc,↓reduceIte,highD]
  omega

theorem zero_a1_emptyD : ¬badD 5 0 1 := by
  simp [badD,lowD]

theorem zero_a1_posD (k : Nat) (hk : k>0) : ¬badD 2 2 (2*k-1) := by
  by_cases hsmall : k=1
  · subst k
    simp [badD,lowD]
  · have hc : ¬(2*k-1<2) := by omega
    simp only [badD,hc,↓reduceIte,highD]
    omega

theorem zero_a_posD (a k : Nat) (ha : a≥2) :
    badD (a-2) 1 (2*k+1) → badD a k 0 := by
  intro h
  by_cases hk : k=0
  · subst k
    simp only [badD, show (1:Nat)<2 by omega, ↓reduceIte,lowD] at h
    simp only [badD, show (0:Nat)<2 by omega, ↓reduceIte,lowD]
    omega
  · have h2 : ¬(2*k+1<2) := by omega
    simp only [badD,h2,↓reduceIte,highD] at h
    simp only [badD, show (0:Nat)<2 by omega, ↓reduceIte,lowD]
    omega

theorem high_a0_evenD (k c : Nat) (hc : c≥4) (hk : k%2=0) :
    badD (2*k+2) 2 (c-3) → badD 0 k c := by
  intro h
  by_cases hs : c=4
  · subst c
    simp only [badD,show (1:Nat)<2 by omega, ↓reduceIte,lowD] at h
    simp only [badD,show ¬((4:Nat)<2) by omega, ↓reduceIte,highD]
    rcases h with h | h | h | h <;> omega
  · have hc2 : ¬(c-3<2) := by omega
    simp only [badD,hc2,↓reduceIte,highD] at h
    simp only [badD,show ¬(c<2) by omega, ↓reduceIte,highD]
    rcases h with h | h | h | h | h | h <;> omega

theorem high_a0_oddD (k c : Nat) (hc : c≥4) (hk : k%2≠0) :
    badD (2*k+3) 0 c → badD 0 k c := by
  intro h
  simp only [badD,show ¬(c<2) by omega, ↓reduceIte,highD] at h ⊢
  rcases h with ⟨hd,ht⟩ | ⟨hd,ht⟩ | ⟨hd,ht⟩ | ⟨hd,ht⟩ | ⟨hd,ht⟩ | ⟨hd,ht⟩
  · exfalso; clear hd; omega
  · exfalso; clear hd; omega
  · exfalso; clear hd; omega
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega)))))
  · exfalso; clear hd; omega
  · rcases ht with ht | ht
    · by_cases hk7 : k%24=7
      · exact Or.inr (Or.inr (Or.inl (by omega)))
      · exact Or.inl (by omega)
    · exfalso; clear hd; omega

theorem high_a_posD (a k c : Nat) (ha : a>0) (hc : c≥4) :
    badD (a-1) (k+1) (c-1) → badD a k c := by
  intro h
  have hc2 : ¬(c-1<2) := by omega
  have hd : (a-1+48-(c-1)%48)%48 = (a+48-c%48)%48 := by omega
  have ht : ((a-1)+(k+1))%96 = (a+k)%96 := by omega
  simp only [badD,hc2,show ¬(c<2) by omega,↓reduceIte,highD] at h ⊢
  rw [hd,ht] at h
  exact h

theorem backward_stepD (a k c a' k' c' : Nat)
    (h : nextC (a,k,c)=some (a',k',c'))
    (hb : badD a' k' c') : badD a k c := by
  by_cases hc1 : c=1
  · subst c
    simp [nextC] at h
    obtain ⟨rfl,rfl,rfl⟩ := h
    exact low_transferD a k hb
  by_cases hc2 : c=2
  · subst c
    simp [nextC] at h
  by_cases hc3 : c=3
  · subst c
    simp [nextC,hc1] at h
    obtain ⟨rfl,rfl,rfl⟩ := h
    exact high_to_low3D a k hb
  by_cases hc0 : c=0
  · subst c
    by_cases ha0 : a=0
    · subst a
      simp [nextC] at h
      obtain ⟨rfl,rfl,rfl⟩ := h
      exact False.elim (zero_a0D k hb)
    by_cases ha1 : a=1
    · subst a
      by_cases hk0 : k=0
      · subst k
        simp [nextC] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        exact False.elim (zero_a1_emptyD hb)
      · simp [nextC,ha0,hk0] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        exact False.elim (zero_a1_posD k (by omega) hb)
    · simp [nextC,ha0,ha1] at h
      obtain ⟨rfl,rfl,rfl⟩ := h
      exact zero_a_posD a k (by omega) hb
  · have hc4 : c≥4 := by omega
    by_cases ha0 : a=0
    · subst a
      by_cases he : k%2=0
      · simp [nextC,hc1,hc2,hc3,hc0,he] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        exact high_a0_evenD k c hc4 he hb
      · simp [nextC,hc1,hc2,hc3,hc0,he] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        exact high_a0_oddD k c hc4 he hb
    · simp [nextC,hc1,hc2,hc3,hc0,ha0] at h
      obtain ⟨rfl,rfl,rfl⟩ := h
      exact high_a_posD a k c (by omega) hc4 hb

#print axioms backward_stepD

end NewCore
