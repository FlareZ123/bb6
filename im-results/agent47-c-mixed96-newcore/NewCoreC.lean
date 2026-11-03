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

def lowC (a k c : Nat) : Prop :=
  (a % 48 = 5 ∧ (a+k+c)%96 = 60) ∨
  (a % 48 = 18 ∧ (k+c)%24 = 19) ∨
  (a % 48 = 28 ∧ (k+c)%24 = 16) ∨
  (a % 48 = 42 ∧ (k+c)%24 = 7)

def highC (a k c : Nat) : Prop :=
  let d := (a + 48 - c%48)%48
  let t := (a+k)%96
  (d=2 ∧ t=57) ∨
  (d=8 ∧ t%24=7) ∨
  (d=15 ∧ t%24=10) ∨
  (d=25 ∧ t%24=17) ∨
  (d=32 ∧ t%24=19) ∨
  (d=39 ∧ t%24=22) ∨
  (d=41 ∧ t%48=27)

def badC (a k c : Nat) : Prop :=
  if c < 2 then lowC a k c else highC a k c

theorem low_transferC (a k : Nat) :
    badC a (k+1) 0 → badC a k 1 := by
  simp only [badC, show (0:Nat)<2 by omega, show (1:Nat)<2 by omega, ↓reduceIte]
  simp only [lowC]
  omega

theorem high_to_low3C (a k : Nat) :
    badC a (k+2) 1 → badC a k 3 := by
  simp only [badC, show (1:Nat)<2 by omega, show ¬((3:Nat)<2) by omega, ↓reduceIte]
  intro h
  simp only [lowC,highC] at *
  rcases h with h | h | h | h
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))

theorem zero_a0C (k : Nat) : ¬badC 1 0 (2*k+2) := by
  have hc : ¬(2*k+2<2) := by omega
  simp only [badC,hc,↓reduceIte,highC]
  omega

theorem zero_a1_emptyC : ¬badC 5 0 1 := by
  simp [badC,lowC]

theorem zero_a1_posC (k : Nat) (hk : k>0) : ¬badC 2 2 (2*k-1) := by
  by_cases hsmall : k=1
  · subst k
    simp [badC,lowC]
  · have hc : ¬(2*k-1<2) := by omega
    simp only [badC,hc,↓reduceIte,highC]
    omega

theorem zero_a_posC (a k : Nat) (ha : a≥2) :
    badC (a-2) 1 (2*k+1) → badC a k 0 := by
  intro h
  by_cases hk : k=0
  · subst k
    simp only [badC, show (1:Nat)<2 by omega, ↓reduceIte,lowC] at h
    simp only [badC, show (0:Nat)<2 by omega, ↓reduceIte,lowC]
    omega
  · have h2 : ¬(2*k+1<2) := by omega
    simp only [badC,h2,↓reduceIte,highC] at h
    simp only [badC, show (0:Nat)<2 by omega, ↓reduceIte,lowC]
    omega

theorem high_a0_evenC (k c : Nat) (hc : c≥4) (hk : k%2=0) :
    badC (2*k+2) 2 (c-3) → badC 0 k c := by
  intro h
  by_cases hs : c=4
  · subst c
    simp only [badC,show (1:Nat)<2 by omega, ↓reduceIte,lowC] at h
    simp only [badC,show ¬((4:Nat)<2) by omega, ↓reduceIte,highC]
    rcases h with h | h | h | h <;> omega
  · have hc2 : ¬(c-3<2) := by omega
    simp only [badC,hc2,↓reduceIte,highC] at h
    simp only [badC,show ¬(c<2) by omega, ↓reduceIte,highC]
    rcases h with h | h | h | h | h | h | h <;> omega

theorem high_a0_oddC (k c : Nat) (hc : c≥4) (hk : k%2≠0) :
    badC (2*k+3) 0 c → badC 0 k c := by
  intro h
  simp only [badC,show ¬(c<2) by omega, ↓reduceIte,highC] at h ⊢
  rcases h with ⟨hd,ht⟩ | ⟨hd,ht⟩ | ⟨hd,ht⟩ | ⟨hd,ht⟩ | ⟨hd,ht⟩ | ⟨hd,ht⟩ | ⟨hd,ht⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))
  · exfalso; clear hd; omega
  · exfalso; clear hd; omega
  · by_cases hk7 : k%24=7
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by omega))))
  · exfalso; clear hd; omega
  · exfalso; clear hd; omega
  · exfalso; clear hd; omega

theorem high_a_posC (a k c : Nat) (ha : a>0) (hc : c≥4) :
    badC (a-1) (k+1) (c-1) → badC a k c := by
  intro h
  have hc2 : ¬(c-1<2) := by omega
  have hd : (a-1+48-(c-1)%48)%48 = (a+48-c%48)%48 := by omega
  have ht : ((a-1)+(k+1))%96 = (a+k)%96 := by omega
  simp only [badC,hc2,show ¬(c<2) by omega,↓reduceIte,highC] at h ⊢
  rw [hd,ht] at h
  exact h

theorem backward_stepC (a k c a' k' c' : Nat)
    (h : nextC (a,k,c)=some (a',k',c'))
    (hb : badC a' k' c') : badC a k c := by
  by_cases hc1 : c=1
  · subst c
    simp [nextC] at h
    obtain ⟨rfl,rfl,rfl⟩ := h
    exact low_transferC a k hb
  by_cases hc2 : c=2
  · subst c
    simp [nextC] at h
  by_cases hc3 : c=3
  · subst c
    simp [nextC,hc1] at h
    obtain ⟨rfl,rfl,rfl⟩ := h
    exact high_to_low3C a k hb
  by_cases hc0 : c=0
  · subst c
    by_cases ha0 : a=0
    · subst a
      simp [nextC] at h
      obtain ⟨rfl,rfl,rfl⟩ := h
      exact False.elim (zero_a0C k hb)
    by_cases ha1 : a=1
    · subst a
      by_cases hk0 : k=0
      · subst k
        simp [nextC] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        exact False.elim (zero_a1_emptyC hb)
      · simp [nextC,ha0,hk0] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        exact False.elim (zero_a1_posC k (by omega) hb)
    · simp [nextC,ha0,ha1] at h
      obtain ⟨rfl,rfl,rfl⟩ := h
      exact zero_a_posC a k (by omega) hb
  · have hc4 : c≥4 := by omega
    by_cases ha0 : a=0
    · subst a
      by_cases he : k%2=0
      · simp [nextC,hc1,hc2,hc3,hc0,he] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        exact high_a0_evenC k c hc4 he hb
      · simp [nextC,hc1,hc2,hc3,hc0,he] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        exact high_a0_oddC k c hc4 he hb
    · simp [nextC,hc1,hc2,hc3,hc0,ha0] at h
      obtain ⟨rfl,rfl,rfl⟩ := h
      exact high_a_posC a k c (by omega) hc4 hb

#print axioms backward_stepC

end NewCore
