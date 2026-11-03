import BackwardMod
set_option maxHeartbeats 0
set_option maxRecDepth 8000
namespace A4Backward192
open A4Backward

def low (a k c : Nat) : Prop :=
  (a%192=35 ∧ (k+c)%192=61) ∨
  (a%96=0 ∧ (k+c)%48=25) ∨
  (a%96=10 ∧ (k+c)%48=19) ∨
  (a%96=34 ∧ (k+c)%48=7) ∨
  (a%96=46 ∧ (k+c)%48=4) ∨
  (a%96=48 ∧ (k+c)%48=1) ∨
  (a%96=58 ∧ (k+c)%48=43) ∨
  (a%96=82 ∧ (k+c)%48=31)

def high (a k c : Nat) : Prop :=
  let d := (a + 96 - c%96)%96
  let t := (a+k)%192
  (d=7 ∧ t%48=26) ∨
  (d=8 ∧ t%48=27) ∨
  (d=17 ∧ t%48=33) ∨
  (d=31 ∧ t%48=38) ∨
  (d=32 ∧ (t%48=39 ∨ t=93)) ∨
  (d=35 ∧ t%96=45) ∨
  (d=43 ∧ t%48=47) ∨
  (d=45 ∧ t%48=46) ∨
  (d=55 ∧ t%48=2) ∨
  (d=56 ∧ t%48=3) ∨
  (d=65 ∧ t%48=9) ∨
  (d=79 ∧ t%48=14) ∨
  (d=80 ∧ t%48=15) ∨
  (d=86 ∧ t%48=21) ∨
  (d=93 ∧ t%48=22)

def bad (a k c : Nat) : Prop :=
  if c<2 then low a k c else high a k c

theorem low_transfer (a k : Nat) : bad a (k+1) 0 → bad a k 1 := by
  simp only [bad, show (0:Nat)<2 by omega, show (1:Nat)<2 by omega, ↓reduceIte]
  simp only [low]
  omega

theorem high_to_low3 (a k : Nat) : bad a (k+2) 1 → bad a k 3 := by
  simp only [bad, show (1:Nat)<2 by omega, show ¬((3:Nat)<2) by omega, ↓reduceIte]
  intro h
  simp only [low, high] at *
  rcases h with h | h | h | h | h | h | h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((by omega)))))))))))))))
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))))))))

#print axioms high_to_low3

theorem zero_a0 (k : Nat) : ¬bad 1 0 (2*k+2) := by
  have hc : ¬(2*k+2<2) := by omega
  simp only [bad,hc,↓reduceIte,high]
  intro h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega

#print axioms zero_a0

theorem zero_a1_empty : ¬bad 5 0 1 := by
  simp [bad,low]

#print axioms zero_a1_empty

theorem zero_a1_pos (k : Nat) (hk : k>0) : ¬bad 2 2 (2*k-1) := by
  by_cases hsmall : k=1
  · subst k
    simp [bad,low]
  · have hc : ¬(2*k-1<2) := by omega
    simp only [bad,hc,↓reduceIte,high]
    intro h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega

#print axioms zero_a1_pos

theorem zero_a_pos (a k : Nat) (ha : a≥2) :
    bad (a-2) 1 (2*k+1) → bad a k 0 := by
  intro h
  by_cases hk : k=0
  · subst k
    simp only [bad, show (1:Nat)<2 by omega, ↓reduceIte,low] at h
    simp only [bad, show (0:Nat)<2 by omega, ↓reduceIte,low]
    rcases h with h | h | h | h | h | h | h | h <;> omega
  · have hc : ¬(2*k+1<2) := by omega
    simp only [bad,hc,↓reduceIte,high] at h
    simp only [bad, show (0:Nat)<2 by omega, ↓reduceIte,low]
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega

#print axioms zero_a_pos

theorem high_a0_even (k c : Nat) (hc : c≥4) (hk : k%2=0) :
    bad (2*k+2) 2 (c-3) → bad 0 k c := by
  intro h
  by_cases hs : c=4
  · subst c
    simp only [bad,show (1:Nat)<2 by omega,↓reduceIte,low] at h
    simp only [bad,show ¬((4:Nat)<2) by omega,↓reduceIte,high]
    rcases h with h | h | h | h | h | h | h | h <;> omega
  · have hc2 : ¬(c-3<2) := by omega
    simp only [bad,hc2,↓reduceIte,high] at h
    simp only [bad,show ¬(c<2) by omega,↓reduceIte,high]
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega

#print axioms high_a0_even

theorem high_a0_odd (k c : Nat) (hc : c≥4) (hk : k%2≠0) :
    bad (2*k+3) 0 c → bad 0 k c := by
  intro h
  simp only [bad,show ¬(c<2) by omega,↓reduceIte,high] at h ⊢
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega

#print axioms high_a0_odd

theorem high_a_pos (a k c : Nat) (ha : a>0) (hc : c≥4) :
    bad (a-1) (k+1) (c-1) → bad a k c := by
  intro h
  have hc2 : ¬(c-1<2) := by omega
  have hd : (a-1+96-(c-1)%96)%96=(a+96-c%96)%96 := by omega
  have ht : ((a-1)+(k+1))%192=(a+k)%192 := by omega
  simp only [bad,hc2,show ¬(c<2) by omega,↓reduceIte,high] at h ⊢
  rw [hd,ht] at h
  exact h

#print axioms high_a_pos

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
end A4Backward192
