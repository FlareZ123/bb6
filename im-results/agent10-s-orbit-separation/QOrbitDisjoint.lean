import Lean.Elab.Tactic.Omega

namespace BB6Agent10

def qNext (q : Nat) : Nat :=
  if q%3=0 then 4*(q/3)
  else if q%3=1 then 4*(q/3)-3
  else 4*(q/3)+1

def bNext (b : Nat) : Nat :=
  if b%3=0 then 4*(b/3)+1
  else if b%3=1 then 4*(b/3)+5
  else 4*(b/3)+8

/-- The published surviving S-section b transition becomes qNext under
    q=b+16. The c-dependent transfer branch is excluded here. -/
theorem qNext_bShift (b : Nat) : qNext (b+16) = bNext b +16 := by
  unfold qNext bNext
  by_cases h0 : b%3=0
  · have hm0 : (b+16)%3≠0 := by omega
    have hm1 : (b+16)%3=1 := by omega
    simp only [ite_eq_left h0, ite_eq_right hm0, ite_eq_left hm1]
    omega
  · by_cases h1 : b%3=1
    · have hm0 : (b+16)%3≠0 := by omega
      have hm1 : (b+16)%3≠1 := by omega
      simp only [ite_eq_right h0, ite_eq_left h1, ite_eq_right hm0, ite_eq_right hm1]
      omega
    · have hm0 : (b+16)%3=0 := by omega
      simp only [ite_eq_right h0, ite_eq_right h1, ite_eq_left hm0]
      omega

def good (q : Nat) : Prop := 16 ≤ q ∧ (q%4=0 ∨ q%4=1)

theorem qNext_grows (q : Nat) (hq : 16≤q) : q < qNext q := by
  unfold qNext
  by_cases h0 : q%3=0
  · simp only [ite_eq_left h0]
    omega
  · simp only [ite_eq_right h0]
    by_cases h1 : q%3=1
    · simp only [ite_eq_left h1]
      omega
    · simp only [ite_eq_right h1]
      omega

theorem qNext_mod4 (q : Nat) (hq : 16≤q) : good (qNext q) := by
  unfold good qNext
  by_cases h0 : q%3=0
  · simp only [ite_eq_left h0]
    omega
  · simp only [ite_eq_right h0]
    by_cases h1 : q%3=1
    · simp only [ite_eq_left h1]
      omega
    · simp only [ite_eq_right h1]
      omega

theorem qNext_injective_good (a b : Nat) (ha : good a) (hb : good b)
    (heq : qNext a = qNext b) : a=b := by
  unfold good at ha hb
  unfold qNext at heq
  by_cases a0 : a%3=0 <;> by_cases b0 : b%3=0
  · simp only [ite_eq_left a0,ite_eq_left b0] at heq
    omega
  · simp only [ite_eq_left a0,ite_eq_right b0] at heq
    by_cases b1 : b%3=1
    · simp only [ite_eq_left b1] at heq
      omega
    · simp only [ite_eq_right b1] at heq
      omega
  · simp only [ite_eq_right a0,ite_eq_left b0] at heq
    by_cases a1 : a%3=1
    · simp only [ite_eq_left a1] at heq
      omega
    · simp only [ite_eq_right a1] at heq
      omega
  · simp only [ite_eq_right a0,ite_eq_right b0] at heq
    by_cases a1 : a%3=1 <;> by_cases b1 : b%3=1
    · simp only [ite_eq_left a1,ite_eq_left b1] at heq
      omega
    · simp only [ite_eq_left a1,ite_eq_right b1] at heq
      omega
    · simp only [ite_eq_right a1,ite_eq_left b1] at heq
      omega
    · simp only [ite_eq_right a1,ite_eq_right b1] at heq
      omega

def qIter : Nat → Nat → Nat
  | 0, q => q
  | n+1, q => qNext (qIter n q)

theorem qIter_add (m n q : Nat) :
    qIter (m+n) q = qIter m (qIter n q) := by
  induction m with
  | zero => simp [qIter]
  | succ m ih =>
    simp only [Nat.succ_add,qIter,ih]

theorem qIter_good (n q : Nat) (hq : good q) : good (qIter n q) := by
  induction n with
  | zero => exact hq
  | succ n ih => exact qNext_mod4 _ ih.1

theorem qIter_grows (n q : Nat) (hq : 16 ≤ q) :
    qIter n q < qIter (n+1) q := by
  have hgood : 16≤qIter n q := by
    induction n with
    | zero => simpa [qIter] using hq
    | succ n ih => exact Nat.le_trans ih (Nat.le_of_lt (qNext_grows _ ih))
  exact qNext_grows _ hgood

theorem qIter_time_mono (i j q : Nat) (hq : 16≤q) (hij : i≤j) :
    qIter i q ≤ qIter j q := by
  induction j with
  | zero =>
      have : i=0 := by omega
      subst i
      exact Nat.le_refl _
  | succ j ih =>
    by_cases hi : i≤j
    · exact Nat.le_trans (ih hi) (Nat.le_of_lt (qIter_grows j q hq))
    · have : i=j+1 := by omega
      subst i
      exact Nat.le_refl _

theorem qIter_cancel (n a b : Nat) (ha : good a) (hb : good b)
    (heq : qIter n a = qIter n b) : a=b := by
  induction n with
  | zero => simpa [qIter] using heq
  | succ n ih =>
    have ga := qIter_good n a ha
    have gb := qIter_good n b hb
    have hstep : qNext (qIter n a) = qNext (qIter n b) := by
      simpa only [qIter] using heq
    exact ih (qNext_injective_good _ _ ga gb hstep)

/-- Any number strictly between consecutive orbit points is missed forever,
    since the map strictly increases once q>=16. -/
theorem qIter_gap_absent (a b k n : Nat) (ha : 16≤a)
    (hl : qIter k a < b) (hu : b < qIter (k+1) a) :
    qIter n a ≠ b := by
  intro he
  by_cases hn : n≤k
  · have hm := qIter_time_mono n k a ha hn
    omega
  · have hm := qIter_time_mono (k+1) n a ha (by omega)
    omega

/-- A general all-time nonmerging theorem for the arithmetic q-coordinate:
    the two increasing invariant-class orbits cannot ever share a q-value if
    the larger seed sits inside a skipped gap of the smaller seed's orbit. -/
theorem qIter_disjoint_of_gap (a b k m n : Nat)
    (ha : good a) (hb : good b) (hab : a<b)
    (hl : qIter k a < b) (hu : b < qIter (k+1) a) :
    qIter m a ≠ qIter n b := by
  intro h
  by_cases hnm : n≤m
  · have hsum : m=n+(m-n) := by omega
    rw [hsum,qIter_add] at h
    have hgood := qIter_good (m-n) a ha
    have hh := qIter_cancel n (qIter (m-n) a) b hgood hb h
    exact qIter_gap_absent a b k (m-n) ha.1 hl hu hh
  · have hsum : n=m+(n-m) := by omega
    rw [hsum,qIter_add] at h
    have hgood := qIter_good (n-m) b hb
    have hh := qIter_cancel m a (qIter (n-m) b) ha hgood h
    have hlo := qIter_time_mono 0 (n-m) b hb.1 (by omega)
    have h0 : qIter 0 b=b := rfl
    omega

theorem q17_avoids_141 (n : Nat) : qIter n 17 ≠ 141 := by
  intro heq
  by_cases hsmall : n≤8
  · have hm := qIter_time_mono n 8 17 (by omega) hsmall
    have h8 : qIter 8 17=125 := by decide
    omega
  · have hm := qIter_time_mono 9 n 17 (by omega) (by omega)
    have h9 : qIter 9 17=165 := by decide
    omega

theorem rooted_q_orbits_disjoint (m n : Nat) : qIter m 17 ≠ qIter n 141 := by
  have ga : good 17 := by simp [good]
  have gb : good 141 := by simp [good]
  have h8 : qIter 8 17=125 := by decide
  have h9 : qIter 9 17=165 := by decide
  have hl : qIter 8 17 < 141 := by omega
  have hu : 141 < qIter (8+1) 17 := by
    change 141 < qIter 9 17
    omega
  exact qIter_disjoint_of_gap 17 141 8 m n ga gb (by omega) hl hu

#print axioms qNext_injective_good
#print axioms qIter_disjoint_of_gap
#print axioms q17_avoids_141
#print axioms rooted_q_orbits_disjoint
end BB6Agent10
