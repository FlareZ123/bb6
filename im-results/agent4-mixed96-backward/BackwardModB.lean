import BackwardMod
set_option maxHeartbeats 0
set_option maxRecDepth 4000

namespace A4BackwardB
open A4Backward

def lowB (a k c : Nat) : Prop :=
  (a % 96 = 29 ∧ (k+c)%96=79) ∨
  (a % 96 = 77 ∧ (k+c)%96=31) ∨
  (a % 48 = 4 ∧ (k+c)%24=16) ∨
  (a % 48 = 18 ∧ (k+c)%24=7) ∨
  (a % 48 = 42 ∧ (k+c)%24=19)

def highB (a k c : Nat) : Prop :=
  let d := (a + 48 - c%48)%48
  let t := (a+k)%96
  (d=1 ∧ t%24=17) ∨
  (d=8 ∧ t%24=19) ∨
  (d=15 ∧ t%24=22) ∨
  (d=17 ∧ t%48=3) ∨
  (d=26 ∧ t=9) ∨
  (d=32 ∧ t%24=7) ∨
  (d=39 ∧ t%24=10)

def badB (a k c : Nat) : Prop :=
  if c < 2 then lowB a k c else highB a k c

theorem low_transfer (a k : Nat) :
    badB a (k+1) 0 → badB a k 1 := by
  simp only [badB, show (0:Nat)<2 by omega, show (1:Nat)<2 by omega, ↓reduceIte]
  simp only [lowB]
  omega

theorem high_to_low3 (a k : Nat) :
    badB a (k+2) 1 → badB a k 3 := by
  simp only [badB, show (1:Nat)<2 by omega, show ¬((3:Nat)<2) by omega, ↓reduceIte]
  intro h
  simp only [lowB,highB] at *
  rcases h with h | h | h | h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))

theorem zero_a0 (k : Nat) :
    ¬badB 1 0 (2*k+2) := by
  have hc : ¬(2*k+2<2) := by omega
  simp only [badB, hc, ↓reduceIte, highB]
  omega

theorem zero_a1_empty : ¬badB 5 0 1 := by
  simp [badB,lowB]

theorem zero_a1_pos (k : Nat) (hk : k>0) :
    ¬badB 2 2 (2*k-1) := by
  by_cases hsmall : k=1
  · subst k
    simp [badB,lowB]
  · have hc : ¬(2*k-1<2) := by omega
    simp only [badB,hc, ↓reduceIte, highB]
    omega

theorem zero_a_pos (a k : Nat) (ha : a≥2) :
    badB (a-2) 1 (2*k+1) → badB a k 0 := by
  intro h
  by_cases hk : k=0
  · subst k
    simp only [badB, show (1:Nat)<2 by omega, ↓reduceIte,lowB] at h
    rcases h with h | h | h | h | h <;> omega
  · have h2 : ¬(2*k+1<2) := by omega
    simp only [badB,h2, ↓reduceIte,highB] at h
    simp only [badB, show (0:Nat)<2 by omega, ↓reduceIte,lowB]
    rcases h with h | h | h | h | h | h | h
    · have cases : (a%48=18 ∧ k%24=7) ∨ (a%48=42 ∧ k%24=19) := by omega
      rcases cases with hh | hh
      · exact Or.inr (Or.inr (Or.inr (Or.inl hh)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hh)))
    · exfalso; omega
    · exfalso; omega
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega

theorem high_a0_even (k c : Nat) (hc : c≥4) (hk : k%2=0) :
    badB (2*k+2) 2 (c-3) → badB 0 k c := by
  intro h
  by_cases hs : c=4
  · subst c
    simp only [badB,show (1:Nat)<2 by omega, ↓reduceIte,lowB] at h
    rcases h with h | h | h | h | h <;> omega
  · have hc2 : ¬(c-3<2) := by omega
    simp only [badB,hc2, ↓reduceIte,highB] at h
    rcases h with h | h | h | h | h | h | h <;> omega

theorem high_a0_odd (k c : Nat) (hc : c≥4) (hk : k%2≠0) :
    badB (2*k+3) 0 c → badB 0 k c := by
  intro h
  simp only [badB,show ¬(c<2) by omega, ↓reduceIte,highB] at h ⊢
  rcases h with ⟨hd,ht⟩ | ⟨_,ht⟩ | ⟨_,ht⟩ | ⟨hd,ht⟩ | ⟨hd,ht⟩ | ⟨_,ht⟩ | ⟨_,ht⟩
  · by_cases hk7 : k%24=7
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))
    · exact Or.inr (Or.inl (by omega))
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
  · exfalso; omega
  · exfalso; omega

theorem high_a_pos (a k c : Nat) (ha : a>0) (hc : c≥4) :
    badB (a-1) (k+1) (c-1) → badB a k c := by
  intro h
  have hc2 : ¬(c-1<2) := by omega
  have hd : (a-1+48-(c-1)%48)%48 = (a+48-c%48)%48 := by omega
  have ht : ((a-1)+(k+1))%96 = (a+k)%96 := by omega
  simp only [badB,hc2,show ¬(c<2) by omega, ↓reduceIte,highB] at h ⊢
  rw [hd,ht] at h
  exact h

theorem backward_step (a k c a' k' c' : Nat)
    (h : nextC (a,k,c)=some (a',k',c'))
    (hb : badB a' k' c') : badB a k c := by
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
end A4BackwardB
