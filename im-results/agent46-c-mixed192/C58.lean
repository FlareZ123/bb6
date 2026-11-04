import CLine
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace BB6.Agent46C58

/-- Exact low two-counter slice of the 192×192×194 reverse core. -/
def low (a w : Nat) : Prop :=
    (a%192=1 ∧ w%96=40) ∨
    (a%192=1 ∧ w%192=142) ∨
    (a%192=15 ∧ w%96=31) ∨
    (a%192=17 ∧ w%96=34) ∨
    (a%192=33 ∧ w%96=25) ∨
    (a%192=39 ∧ w%96=19) ∨
    (a%192=49 ∧ w%96=16) ∨
    (a%192=63 ∧ w%96=7) ∨
    (a%192=81 ∧ w%96=1) ∨
    (a%192=87 ∧ w%96=91) ∨
    (a%192=97 ∧ w%96=88) ∨
    (a%192=111 ∧ w%96=79) ∨
    (a%192=113 ∧ w%96=82) ∨
    (a%192=129 ∧ w%96=73) ∨
    (a%192=135 ∧ w%96=67) ∨
    (a%192=141 ∧ w%96=70) ∨
    (a%192=145 ∧ w%96=64) ∨
    (a%192=159 ∧ w%96=55) ∨
    (a%192=177 ∧ w%96=49) ∨
    (a%192=183 ∧ w%96=43)

/-- The high counter core, with d=(a-c) modulo 192. -/
def high (a k c : Nat) : Prop :=
    ((a+192-c%192)%192=12 ∧ (a+k)%96=43) ∨
    ((a+192-c%192)%192=13 ∧ (a+k)%96=46) ∨
    ((a+192-c%192)%192=14 ∧ (a+k)%96=48) ∨
    ((a+192-c%192)%192=25 ∧ (a+k)%96=54) ∨
    ((a+192-c%192)%192=30 ∧ (a+k)%96=55) ∨
    ((a+192-c%192)%192=36 ∧ (a+k)%96=55) ∨
    ((a+192-c%192)%192=43 ∧ (a+k)%96=62) ∨
    ((a+192-c%192)%192=46 ∧ (a+k)%96=62) ∨
    ((a+192-c%192)%192=49 ∧ (a+k)%96=68) ∨
    ((a+192-c%192)%192=60 ∧ (a+k)%96=67) ∨
    ((a+192-c%192)%192=61 ∧ (a+k)%96=70) ∨
    ((a+192-c%192)%192=76 ∧ (a+k)%96=80) ∨
    ((a+192-c%192)%192=78 ∧ (a+k)%96=79) ∨
    ((a+192-c%192)%192=84 ∧ (a+k)%96=79) ∨
    ((a+192-c%192)%192=91 ∧ (a+k)%96=86) ∨
    ((a+192-c%192)%192=94 ∧ (a+k)%96=86) ∨
    ((a+192-c%192)%192=108 ∧ (a+k)%96=91) ∨
    ((a+192-c%192)%192=109 ∧ (a+k)%96=94) ∨
    ((a+192-c%192)%192=110 ∧ (a+k)%96=0) ∨
    ((a+192-c%192)%192=121 ∧ (a+k)%96=6) ∨
    ((a+192-c%192)%192=126 ∧ (a+k)%96=7) ∨
    ((a+192-c%192)%192=132 ∧ (a+k)%96=7) ∨
    ((a+192-c%192)%192=138 ∧ (a+k)%96=16) ∨
    ((a+192-c%192)%192=139 ∧ (a+k)%96=14) ∨
    ((a+192-c%192)%192=142 ∧ (a+k)%96=14) ∨
    ((a+192-c%192)%192=156 ∧ (a+k)%96=19) ∨
    ((a+192-c%192)%192=157 ∧ (a+k)%96=22) ∨
    ((a+192-c%192)%192=172 ∧ (a+k)%96=32) ∨
    ((a+192-c%192)%192=174 ∧ (a+k)%96=31) ∨
    ((a+192-c%192)%192=180 ∧ (a+k)%96=31) ∨
    ((a+192-c%192)%192=187 ∧ (a+k)%96=38) ∨
    ((a+192-c%192)%192=190 ∧ (a+k)%96=38) ∨
    ((a+192-c%192)%192=190 ∧ (a+k)%192=140)

def bad (a k c : Nat) : Prop :=
    if c<2 then low a (k+c) else high a k c

theorem low_transfer (a k : Nat) : bad a (k+1) 0 → bad a k 1 := by
  simpa only [bad, show (0:Nat)<2 by omega, show (1:Nat)<2 by omega, ↓reduceIte, Nat.add_zero] using (id : low a (k+1) → low a (k+1))

theorem high_to_low3 (a k : Nat) : bad a (k+2) 1 → bad a k 3 := by
  simp only [bad, show (1:Nat)<2 by omega, show ¬((3:Nat)<2) by omega, ↓reduceIte]
  intro h
  simp only [low, high] at *
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩))))))))))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega,by omega⟩))))))))))))))))))))))))))))))))
  · exact Or.inl (⟨by omega,by omega⟩)
  · exact Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩)))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩)))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩)))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩)))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩)))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩)))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩))))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩)))))))))))))))))))))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩))))))))))))))))))))))))))))))

theorem zero_a0 (k : Nat) : ¬bad 1 0 (2*k+2) := by
  intro h
  have hc : ¬(2*k+2<2) := by omega
  simp only [bad,hc,↓reduceIte,high] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega

theorem zero_a1_empty : ¬bad 5 0 1 := by
  simp [bad,low]

theorem zero_a1_pos (k : Nat) (hk : k>0) : ¬bad 2 2 (2*k-1) := by
  intro h
  by_cases hs : k=1
  · subst k
    simp [bad,low] at h
  · have hc : ¬(2*k-1<2) := by omega
    simp only [bad,hc,↓reduceIte,high] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega

theorem zero_a_pos (a k : Nat) (ha : a≥2) :
    bad (a-2) 1 (2*k+1) → bad a k 0 := by
  intro h
  by_cases hk : k=0
  · subst k
    simp only [bad,show (1:Nat)<2 by omega,↓reduceIte,low] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  · have hc : ¬(2*k+1<2) := by omega
    simp only [bad,hc,↓reduceIte,high] at h
    simp only [bad,show (0:Nat)<2 by omega,↓reduceIte,low,Nat.add_zero]
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exfalso; omega
    · exfalso; omega
    · by_cases ha : a%192=49
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩)))))))))))))))))
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · by_cases ha : a%192=63
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩))))))))))))))))))
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · by_cases ha : a%192=81
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩)))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩)))))))))))))))))))
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · by_cases ha : a%192=87
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by omega,by omega⟩)))))))))))))))))))
    · exfalso; omega
    · exfalso; omega
    · by_cases ha : a%192=1
      · exact Or.inl (⟨by omega,by omega⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩)))))))))))
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · by_cases ha : a%192=17
      · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩)))))))))))))
    · exfalso; omega
    · by_cases ha : a%192=15
      · exact Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩))))))))))))
    · exfalso; omega
    · exfalso; omega
    · by_cases ha : a%192=33
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩))))))))))))))
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · by_cases ha : a%192=39
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩)))))))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩))))))))))))))))

theorem high_a0_even (k c : Nat) (hc : c≥4) (hk : k%2=0) :
    bad (2*k+2) 2 (c-3) → bad 0 k c := by
  intro h
  by_cases hs : c=4
  · subst c
    simp only [bad,show (1:Nat)<2 by omega,↓reduceIte,low] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  · have hc2 : ¬(c-3<2) := by omega
    simp only [bad,hc2,↓reduceIte,high] at h
    simp only [bad,show ¬(c<2) by omega,↓reduceIte,high]
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exfalso; omega
    · exfalso; omega
    · by_cases hkr : k%96=70
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩)))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩)))))))))))))))))))))))))))
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · by_cases hkr : k%96=80
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩))))))))))))))))))))))))))))
    · exfalso; omega
    · exfalso; omega
    · by_cases hkr : k%96=86
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩)))))))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩)))))))))))))))))))))))))))))))
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · by_cases hkr : k%96=46
      · exact Or.inr (Or.inl (⟨by omega,by omega⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩))))))))))))))))))
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · by_cases hkr : k%96=54
      · exact Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩))))))))))))))))))))
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · by_cases hkr : k%96=62
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩))))))))))))))))))))))))
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by omega,by omega⟩)))))))))

theorem high_a0_odd (k c : Nat) (hc : c≥4) (hk : k%2≠0) :
    bad (2*k+3) 0 c → bad 0 k c := by
  intro h
  simp only [bad,show ¬(c<2) by omega,↓reduceIte,high] at h ⊢
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
theorem high_a_pos (a k c : Nat) (ha : a>0) (hc : c≥4) :
    bad (a-1) (k+1) (c-1) → bad a k c := by
  intro h
  have hc2 : ¬(c-1<2) := by omega
  have hd : ((a-1+192-(c-1)%192)%192) = ((a+192-c%192)%192) := by omega
  have ht : ((a-1)+(k+1))%96 = (a+k)%96 := by omega
  have ht2 : ((a-1)+(k+1))%192 = (a+k)%192 := by omega
  simp only [bad,hc2,show ¬(c<2) by omega,↓reduceIte,high] at h ⊢
  rw [hd,ht,ht2] at h
  exact h

theorem backward (a k c a' k' c' : Nat)
    (h : BB6CLine.nextC (a,k,c)=some (a',k',c'))
    (hb : bad a' k' c') : bad a k c := by
  rcases c with _ | _ | _ | _ | d
  · rcases a with _ | _ | a
    · simp only [BB6CLine.nextC,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl,rfl⟩ := h
      exact False.elim (zero_a0 k hb)
    · rcases k with _ | k
      · simp only [BB6CLine.nextC,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        exact False.elim (zero_a1_empty hb)
      · simp only [BB6CLine.nextC,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        exact False.elim (zero_a1_pos (k+1) (by omega) hb)
    · simp only [BB6CLine.nextC,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl,rfl⟩ := h
      exact zero_a_pos (a+2) k (by omega) hb
  · simp only [BB6CLine.nextC,Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl,rfl⟩ := h
    exact low_transfer a k hb
  · simp [BB6CLine.nextC] at h
  · simp only [BB6CLine.nextC,Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,rfl,rfl⟩ := h
    exact high_to_low3 a k hb
  · rcases a with _ | a
    · by_cases he : k%2=0
      · simp only [BB6CLine.nextC,he,↓reduceIte,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        have hke : 4*(k/2)+2 = 2*k+2 := by omega
        have hce : d+4-3=d+1 := by omega
        rw [hke,←hce] at hb
        exact high_a0_even k (d+4) (by omega) he hb
      · simp only [BB6CLine.nextC,he,↓reduceIte,Option.some.injEq,Prod.mk.injEq] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        have hke : 4*(k/2)+5 = 2*k+3 := by omega
        rw [hke] at hb
        exact high_a0_odd k (d+4) (by omega) he hb
    · simp only [BB6CLine.nextC,Option.some.injEq,Prod.mk.injEq] at h
      obtain ⟨rfl,rfl,rfl⟩ := h
      exact high_a_pos (a+1) k (d+4) (by omega) (by omega) hb

theorem root_safe : ¬bad 5 0 1 := by simp [bad,low]

theorem blank_avoids_bad (s : Nat × Nat × Nat) (h : BB6CLine.Reach s) :
    ¬bad s.1 s.2.1 s.2.2 := by
  induction h with
  | init => exact root_safe
  | next s t _ hstep ih =>
      intro hb
      apply ih
      rcases s with ⟨a,k,c⟩
      rcases t with ⟨a',k',c'⟩
      exact backward a k c a' k' c' hstep hb

theorem first_142_mod192_unreachable (k : Nat) (hk : k%192=142) :
    ¬ BB6CLine.Reach (1,k,0) := by
  intro hr
  apply blank_avoids_bad (1,k,0) hr
  change low 1 k
  unfold low
  exact Or.inr (Or.inl ⟨by decide,hk⟩)

#print axioms first_142_mod192_unreachable
end BB6.Agent46C58
