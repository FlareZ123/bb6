import Std
set_option maxHeartbeats 0
set_option maxRecDepth 4000

namespace A4Backward

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

def low (a k c : Nat) : Prop :=
  (a % 96 = 13 ∧ (k+c)%96=31) ∨
  (a % 48 = 18 ∧ (k+c)%24=23) ∨
  (a % 48 = 20 ∧ (k+c)%24=0) ∨
  (a % 48 = 42 ∧ (k+c)%24=11)

def high (a k c : Nat) : Prop :=
  let d := (a + 48 - c%48)%48
  let t := (a+k)%96
  (d=0 ∧ t%24=7) ∨
  (d=10 ∧ t=41) ∨
  (d=15 ∧ t%24=14) ∨
  (d=17 ∧ (t%24=17 ∨ t=19 ∨ t=67)) ∨
  (d=24 ∧ t%24=19) ∨
  (d=39 ∧ t%24=2)

def bad (a k c : Nat) : Prop :=
  if c < 2 then low a k c else high a k c

theorem low_transfer (a k : Nat) :
    bad a (k+1) 0 → bad a k 1 := by
  simp only [bad, show (0:Nat)<2 by omega, show (1:Nat)<2 by omega, ↓reduceIte]
  simp only [low]
  omega

theorem high_to_low3 (a k : Nat) :
    bad a (k+2) 1 → bad a k 3 := by
  simp only [bad, show (1:Nat)<2 by omega, show ¬((3:Nat)<2) by omega, ↓reduceIte]
  intro h
  simp only [low,high] at *
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega)))))

theorem zero_a0 (k : Nat) :
    ¬bad 1 0 (2*k+2) := by
  have hc : ¬(2*k+2<2) := by omega
  simp only [bad, hc, ↓reduceIte, high]
  omega

theorem zero_a1_empty : ¬bad 5 0 1 := by
  simp [bad,low]

theorem zero_a1_pos (k : Nat) (hk : k>0) :
    ¬bad 2 2 (2*k-1) := by
  by_cases hsmall : k=1
  · subst k
    simp [bad,low]
  · have hc : ¬(2*k-1<2) := by omega
    simp only [bad,hc, ↓reduceIte, high]
    omega

theorem zero_a_pos (a k : Nat) (ha : a≥2) :
    bad (a-2) 1 (2*k+1) → bad a k 0 := by
  intro h
  by_cases hk : k=0
  · subst k
    simp only [bad, show (1:Nat)<2 by omega, ↓reduceIte,low] at h
    omega
  · have h2 : ¬(2*k+1<2) := by omega
    simp only [bad,h2, ↓reduceIte, high] at h
    simp only [bad, show (0:Nat)<2 by omega, ↓reduceIte,low]
    omega

theorem high_a0_even (k c : Nat) (hc : c≥4) (hk : k%2=0) :
    bad (2*k+2) 2 (c-3) → bad 0 k c := by
  intro h
  by_cases hs : c=4
  · subst c
    simp only [bad,show (1:Nat)<2 by omega, ↓reduceIte,low] at h
    rcases h with h | h | h | h <;> omega
  · have hc2 : ¬(c-3<2) := by omega
    simp only [bad,hc2, ↓reduceIte,high] at h
    rcases h with h | h | h | h | h | h
    · omega
    · omega
    · omega
    · rcases h with ⟨_,ht⟩
      rcases ht with ht | ht | ht <;> omega
    · omega
    · omega

theorem high_a0_odd (k c : Nat) (hc : c≥4) (hk : k%2≠0) :
    bad (2*k+3) 0 c → bad 0 k c := by
  intro h
  simp only [bad,show ¬(c<2) by omega, ↓reduceIte,high] at h ⊢
  rcases h with ⟨_,ht⟩ | ⟨hd,ht⟩ | ⟨_,ht⟩ | ⟨hd,ht⟩ | ⟨_,ht⟩ | ⟨_,ht⟩
  · exfalso; omega
  · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
    constructor
    · omega
    · right; omega
  · exfalso; omega
  · rcases ht with ht | ht | ht
    · by_cases hk7 : k%24=7
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
    · exfalso; omega
    · exfalso; omega
  · exfalso; omega
  · exfalso; omega

theorem high_a_pos (a k c : Nat) (ha : a>0) (hc : c≥4) :
    bad (a-1) (k+1) (c-1) → bad a k c := by
  intro h
  have hc2 : ¬(c-1<2) := by omega
  have hd : (a-1+48-(c-1)%48)%48 = (a+48-c%48)%48 := by omega
  have ht : ((a-1)+(k+1))%96 = (a+k)%96 := by omega
  simp only [bad,hc2,show ¬(c<2) by omega, ↓reduceIte,high] at h ⊢
  rw [hd,ht] at h
  exact h

theorem backward_step (a k c a' k' c' : Nat)
    (h : nextC (a,k,c)=some (a',k',c'))
    (hb : bad a' k' c') : bad a k c := by
  by_cases hc1 : c=1
  · subst c
    simp [nextC] at h
    obtain ⟨rfl,rfl,rfl⟩ := h
    exact low_transfer a k hb
  by_cases hc2 : c=2
  · subst c
    simp [nextC] at h
  by_cases hc3 : c=3
  · subst c
    simp [nextC,hc1] at h
    obtain ⟨rfl,rfl,rfl⟩ := h
    exact high_to_low3 a k hb
  by_cases hc0 : c=0
  · subst c
    by_cases ha0 : a=0
    · subst a
      simp [nextC] at h
      obtain ⟨rfl,rfl,rfl⟩ := h
      exact False.elim (zero_a0 k hb)
    by_cases ha1 : a=1
    · subst a
      by_cases hk0 : k=0
      · subst k
        simp [nextC] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        exact False.elim (zero_a1_empty hb)
      · simp [nextC,ha0,hk0] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        exact False.elim (zero_a1_pos k (by omega) hb)
    · simp [nextC,ha0,ha1] at h
      obtain ⟨rfl,rfl,rfl⟩ := h
      exact zero_a_pos a k (by omega) hb
  · have hc4 : c≥4 := by omega
    by_cases ha0 : a=0
    · subst a
      by_cases he : k%2=0
      · simp [nextC,hc1,hc2,hc3,hc0,he] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        exact high_a0_even k c hc4 he hb
      · simp [nextC,hc1,hc2,hc3,hc0,he] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        exact high_a0_odd k c hc4 he hb
    · simp [nextC,hc1,hc2,hc3,hc0,ha0] at h
      obtain ⟨rfl,rfl,rfl⟩ := h
      exact high_a_pos a k c (by omega) hc4 hb

#print axioms backward_step
#print axioms low_transfer
#print axioms high_to_low3
#print axioms high_a0_even
#print axioms high_a0_odd
#print axioms high_a_pos
end A4Backward
