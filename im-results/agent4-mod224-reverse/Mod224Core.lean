import SourceBridge

set_option maxHeartbeats 0

namespace A4Mod224

open A4Backward

def low0 (a k : Nat) : Prop :=
  (a%224=13 ∧ k%224=191) ∨ (a%112=18 ∧ k%56=15) ∨
  (a%112=74 ∧ k%56=43) ∨ (a%112=100 ∧ k%56=32)
def low1 (a k : Nat) : Prop :=
  (a%224=13 ∧ k%224=190) ∨ (a%112=18 ∧ k%56=14) ∨
  (a%112=74 ∧ k%56=42) ∨ (a%112=100 ∧ k%56=31)
def low3 (a k : Nat) : Prop :=
  (a%224=13 ∧ k%224=188) ∨ (a%112=18 ∧ k%56=12) ∨
  (a%112=74 ∧ k%56=40) ∨ (a%112=100 ∧ k%56=29)
def high (a k c : Nat) : Prop :=
  (a%112=(c+10)%112 ∧ (a+k)%224=201) ∨
  (a%112=(c+15)%112 ∧ (a+k)%56=30) ∨
  (a%112=(c+24)%112 ∧ (a+k)%56=35) ∨
  (a%112=(c+33)%112 ∧ (a+k)%112=99) ∨
  (a%112=(c+71)%112 ∧ (a+k)%56=2) ∨
  (a%112=(c+80)%112 ∧ (a+k)%56=7) ∨
  (a%112=(c+97)%112 ∧ (a+k)%56=17)
def bad (a k c : Nat) : Prop :=
  if c=0 then low0 a k
  else if c=1 then low1 a k
  else if c=3 then low3 a k
  else if 4≤c then high a k c
  else False

theorem bad_high (a k c : Nat) (hc : 4≤c) : bad a k c ↔ high a k c := by
  have h0 : c≠0 := by omega
  have h1 : c≠1 := by omega
  have h3 : c≠3 := by omega
  simp [bad,h0,h1,h3,hc]

theorem one_back (a k : Nat) (h : bad a (k+1) 0) : bad a k 1 := by
  simp [bad,low0,low1] at h ⊢
  rcases h with ha|hb|hc|hd
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

theorem three_back (a k : Nat) (h : bad a (k+2) 1) : bad a k 3 := by
  simp [bad,low1,low3] at h ⊢
  rcases h with ha|hb|hc|hd
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (Or.inl (by omega)))
  · exact Or.inr (Or.inr (Or.inr (by omega)))

theorem zero_zero (k : Nat) : ¬ bad 1 0 (2*k+2) := by
  intro h
  by_cases hk : k=0
  · subst k
    simp [bad] at h
  · have hc : 4 ≤ 2*k+2 := by omega
    have hh := (bad_high 1 0 (2*k+2) hc).mp h
    rcases hh with h|h|h|h|h|h|h <;> omega

theorem zero_one_empty : ¬bad 5 0 1 := by simp [bad,low1]

theorem zero_one_pos (k : Nat) (hk : 0<k) : ¬bad 2 2 (2*k-1) := by
  intro h
  by_cases hk1 : k=1
  · subst k
    simp [bad,low1] at h
  · by_cases hk2 : k=2
    · subst k
      simp [bad,low3] at h
    · have hc : 4 ≤ 2*k-1 := by omega
      have hh := (bad_high 2 2 (2*k-1) hc).mp h
      rcases hh with h|h|h|h|h|h|h <;> omega

theorem zero_pos (a k : Nat) (ha : 2≤a) : bad (a-2) 1 (2*k+1) → bad a k 0 := by
  intro h
  by_cases hk0 : k=0
  · subst k
    simp [bad,low1] at h
  · by_cases hk1 : k=1
    · subst k
      simp [bad,low3] at h
    · have hc : 4 ≤ 2*k+1 := by omega
      have hh := (bad_high (a-2) 1 (2*k+1) hc).mp h
      change low0 a k
      rcases hh with h|h|h|h|h|h|h
      · exfalso; omega
      · exfalso; omega
      · exfalso; omega
      · exact Or.inr (Or.inr (Or.inr (by omega)))
      · exfalso; omega
      · exfalso; omega
      · have hc : (a%112=18 ∧ k%56=15) ∨ (a%112=74 ∧ k%56=43) := by omega
        rcases hc with hc1|hc2
        · exact Or.inr (Or.inl hc1)
        · exact Or.inr (Or.inr (Or.inl hc2))

theorem high_zero_even (k c : Nat) (hc : 4≤c) (he : k%2=0) :
    ¬bad (2*k+2) 2 (c-3) := by
  intro h
  by_cases hc4 : c=4
  · subst c
    simp [bad,low1] at h
  · by_cases hc5 : c=5
    · subst c
      simp [bad] at h
    · by_cases hc6 : c=6
      · subst c
        simp [bad,low3] at h
      · have hn : 4≤c-3 := by omega
        have hh := (bad_high (2*k+2) 2 (c-3) hn).mp h
        rcases hh with h|h|h|h|h|h|h <;> omega

theorem high_zero_odd (k c : Nat) (hc : 4≤c) (ho : k%2≠0)
    (h : bad (2*k+3) 0 c) : bad 0 k c := by
  have hh := (bad_high (2*k+3) 0 c hc).mp h
  apply (bad_high 0 k c hc).mpr
  rcases hh with ha|hb|hcc|hd|he|hf|hg
  · exact Or.inr (Or.inr (Or.inr (by omega)))
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · have hcases : (c%112=32 ∧ k%56=7) ∨ (c%112=88 ∧ k%56=35) := by omega
    rcases hcases with hsmall|hlarge
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega)))))
    · exact Or.inr (Or.inr (by omega))

theorem high_pos (a k c : Nat) (ha : 0<a) (hc : 4≤c)
    (h : bad (a-1) (k+1) (c-1)) : bad a k c := by
  by_cases hc4 : c=4
  · subst c
    have hlow : low3 (a-1) (k+1) := by simpa [bad] using h
    apply (bad_high a k 4 (by decide)).mpr
    rcases hlow with h|h|h|h
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by omega))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))
  · have hn : 4≤c-1 := by omega
    have hh := (bad_high (a-1) (k+1) (c-1) hn).mp h
    apply (bad_high a k c hc).mpr
    rcases hh with h|h|h|h|h|h|h
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))

/-- Exact universal predecessor-closure, including exceptional zero-counter
    and parity cases, of a seven-class modular reverse core. -/
theorem backward (a k c ap kp cp : Nat)
    (h : A4Backward.nextC (a,k,c)=some (ap,kp,cp))
    (hb : bad ap kp cp) : bad a k c := by
  by_cases hc1 : c=1
  · subst c
    simp [A4Backward.nextC] at h
    obtain ⟨rfl,rfl,rfl⟩ := h
    exact one_back a k hb
  by_cases hc2 : c=2
  · subst c
    simp [A4Backward.nextC] at h
  by_cases hc3 : c=3
  · subst c
    simp [A4Backward.nextC,hc1] at h
    obtain ⟨rfl,rfl,rfl⟩ := h
    exact three_back a k hb
  by_cases hc0 : c=0
  · subst c
    by_cases ha0 : a=0
    · subst a
      simp [A4Backward.nextC] at h
      obtain ⟨rfl,rfl,rfl⟩ := h
      exact False.elim (zero_zero k hb)
    by_cases ha1 : a=1
    · subst a
      by_cases hk0 : k=0
      · subst k
        simp [A4Backward.nextC] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        exact False.elim (zero_one_empty hb)
      · simp [A4Backward.nextC,ha0,hk0] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        exact False.elim (zero_one_pos k (by omega) hb)
    · simp [A4Backward.nextC,ha0,ha1] at h
      obtain ⟨rfl,rfl,rfl⟩ := h
      exact zero_pos a k (by omega) hb
  · have hc4 : 4 ≤ c := by omega
    by_cases ha0 : a=0
    · subst a
      by_cases he : k%2=0
      · simp [A4Backward.nextC,hc1,hc2,hc3,hc0,he] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        exact False.elim (high_zero_even k c hc4 he hb)
      · simp [A4Backward.nextC,hc1,hc2,hc3,hc0,he] at h
        obtain ⟨rfl,rfl,rfl⟩ := h
        exact high_zero_odd k c hc4 he hb
    · simp [A4Backward.nextC,hc1,hc2,hc3,hc0,ha0] at h
      obtain ⟨rfl,rfl,rfl⟩ := h
      exact high_pos a k c (by omega) hc4 hb

/-- True original Machine C accelerated blank orbit never reaches
    this inverse-closed cone. The bridge is the previously source-checked
    A4Backward.nextC_source_equal, not a copied assumption. -/
theorem source_blank_never_bad (s : Nat × Nat × Nat)
    (h : BB6CLine.Reach s) : ¬ bad s.1 s.2.1 s.2.2 := by
  induction h with
  | init => simp [bad,low1]
  | next x y hx hs ih =>
      rcases x with ⟨a,k,c⟩
      rcases y with ⟨ap,kp,cp⟩
      intro hb
      have he : A4Backward.nextC (a,k,c) = some (ap,kp,cp) := by
        rw [A4Backward.nextC_source_equal]
        exact hs
      exact ih (backward a k c ap kp cp he hb)

/-- Excludes every natural c=0 source orbit target in the full cylinder
    (a,k) ≡ (13,191) mod 224 at all times. -/
theorem source_no_mod224_13_191 (a k : Nat)
    (ha : a%224=13) (hk : k%224=191)
    (hr : BB6CLine.Reach (a,k,0)) : False := by
  have hh := source_blank_never_bad (a,k,0) hr
  apply hh
  simp [bad,low0,ha,hk]

#print axioms backward
#print axioms source_blank_never_bad
#print axioms source_no_mod224_13_191

end A4Mod224
