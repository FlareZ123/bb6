import Lean
set_option maxRecDepth 8192
set_option maxHeartbeats 10000000
namespace Agent23N14

/-- Exact dyadic shadow states for critical P1 n=16*(4096*r)+14. -/
def State (r m z : Nat) : Prop :=
  (m = 0 ∧ z = 8 + 32768*r) ∨
  (m = 1 ∧ z = 13 + 49152*r) ∨
  (m = 2 ∧ z = 16 + 57344*r) ∨
  (m = 3 ∧ z = 11 + 36864*r) ∨
  (m = 3 ∧ z = 18 + 61440*r) ∨
  (m = 4 ∧ z = 11 + 34816*r) ∨
  (m = 4 ∧ z = 16 + 51200*r) ∨
  (m = 5 ∧ z = 13 + 39936*r) ∨
  (m = 5 ∧ z = 19 + 58368*r) ∨
  (m = 6 ∧ z = 18 + 52736*r) ∨
  (m = 6 ∧ z = 21 + 61952*r) ∨
  (m = 7 ∧ z = 14 + 39168*r) ∨
  (m = 7 ∧ z = 21 + 59136*r) ∨
  (m = 8 ∧ z = 17 + 45952*r) ∨
  (m = 8 ∧ z = 23 + 62336*r)

/-- The necessary recurrence of odd-output source inversions, written as arithmetic. -/
def Step (r m z m' z' : Nat) : Prop :=
  ∃ t v : Nat, z = 2^t*v ∧ m' = m+t+1 ∧
    2*z'+1 = 65536*r + 19 + m + t + v

private theorem state_nonzero_mod32 (r m z : Nat) (h : State r m z) : z % 32 ≠ 0 := by
  rcases h with ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩
  all_goals omega

private theorem depth_bound (r m z t : Nat) (h : State r m z)
    (hd : 2^t ∣ z) : t < 5 := by
  by_cases hh : t < 5
  · exact hh
  have h5 : 5 ≤ t := by omega
  have h32 : 32 ∣ z := Nat.dvd_trans (Nat.pow_dvd_pow 2 h5) hd
  exfalso
  exact (state_nonzero_mod32 r m z h) (Nat.mod_eq_zero_of_dvd h32)

theorem state_root (r : Nat) : State r 0 (32768*r+8) := by
  exact Or.inl ⟨rfl, by omega⟩

theorem state_step (r m z m' z' : Nat)
    (h : State r m z) (he : Step r m z m' z') : State r m' z' := by
  obtain ⟨t, v, hdiv, hm, hnext⟩ := he
  have ht : t < 5 := depth_bound r m z t h ⟨v, hdiv⟩
  have htcase : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
  rcases h with ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩
  all_goals subst m
  all_goals subst z
  · rcases htcase with h0 | h1 | h2 | h3 | h4
    all_goals subst t
    ·
      have hmp : m' = 1 := by omega
      have hzp : z' = 13 + 49152*r := by omega
      exact Or.inr (Or.inl ⟨hmp, hzp⟩)
    ·
      omega
    ·
      have hmp : m' = 3 := by omega
      have hzp : z' = 11 + 36864*r := by omega
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hmp, hzp⟩)))
    ·
      have hmp : m' = 4 := by omega
      have hzp : z' = 11 + 34816*r := by omega
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hmp, hzp⟩)))))
    ·
      omega
  · rcases htcase with h0 | h1 | h2 | h3 | h4
    all_goals subst t
    ·
      have hmp : m' = 2 := by omega
      have hzp : z' = 16 + 57344*r := by omega
      exact Or.inr (Or.inr (Or.inl ⟨hmp, hzp⟩))
    ·
      omega
    ·
      omega
    ·
      omega
    ·
      omega
  · rcases htcase with h0 | h1 | h2 | h3 | h4
    all_goals subst t
    ·
      have hmp : m' = 3 := by omega
      have hzp : z' = 18 + 61440*r := by omega
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hmp, hzp⟩))))
    ·
      omega
    ·
      have hmp : m' = 5 := by omega
      have hzp : z' = 13 + 39936*r := by omega
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hmp, hzp⟩)))))))
    ·
      omega
    ·
      omega
  · rcases htcase with h0 | h1 | h2 | h3 | h4
    all_goals subst t
    ·
      have hmp : m' = 4 := by omega
      have hzp : z' = 16 + 51200*r := by omega
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hmp, hzp⟩))))))
    ·
      omega
    ·
      omega
    ·
      omega
    ·
      omega
  · rcases htcase with h0 | h1 | h2 | h3 | h4
    all_goals subst t
    ·
      omega
    ·
      omega
    ·
      omega
    ·
      omega
    ·
      omega
  · rcases htcase with h0 | h1 | h2 | h3 | h4
    all_goals subst t
    ·
      omega
    ·
      omega
    ·
      omega
    ·
      omega
    ·
      omega
  · rcases htcase with h0 | h1 | h2 | h3 | h4
    all_goals subst t
    ·
      have hmp : m' = 5 := by omega
      have hzp : z' = 19 + 58368*r := by omega
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hmp, hzp⟩))))))))
    ·
      omega
    ·
      have hmp : m' = 7 := by omega
      have hzp : z' = 14 + 39168*r := by omega
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hmp, hzp⟩)))))))))))
    ·
      omega
    ·
      omega
  · rcases htcase with h0 | h1 | h2 | h3 | h4
    all_goals subst t
    ·
      have hmp : m' = 6 := by omega
      have hzp : z' = 18 + 52736*r := by omega
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hmp, hzp⟩)))))))))
    ·
      omega
    ·
      omega
    ·
      omega
    ·
      omega
  · rcases htcase with h0 | h1 | h2 | h3 | h4
    all_goals subst t
    ·
      have hmp : m' = 6 := by omega
      have hzp : z' = 21 + 61952*r := by omega
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hmp, hzp⟩))))))))))
    ·
      omega
    ·
      omega
    ·
      omega
    ·
      omega
  · rcases htcase with h0 | h1 | h2 | h3 | h4
    all_goals subst t
    ·
      have hmp : m' = 7 := by omega
      have hzp : z' = 21 + 59136*r := by omega
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hmp, hzp⟩))))))))))))
    ·
      have hmp : m' = 8 := by omega
      have hzp : z' = 17 + 45952*r := by omega
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hmp, hzp⟩)))))))))))))
    ·
      omega
    ·
      omega
    ·
      omega
  · rcases htcase with h0 | h1 | h2 | h3 | h4
    all_goals subst t
    ·
      omega
    ·
      omega
    ·
      omega
    ·
      omega
    ·
      omega
  · rcases htcase with h0 | h1 | h2 | h3 | h4
    all_goals subst t
    ·
      omega
    ·
      omega
    ·
      omega
    ·
      omega
    ·
      omega
  · rcases htcase with h0 | h1 | h2 | h3 | h4
    all_goals subst t
    ·
      have hmp : m' = 8 := by omega
      have hzp : z' = 23 + 62336*r := by omega
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨hmp, hzp⟩))))))))))))))
    ·
      omega
    ·
      omega
    ·
      omega
    ·
      omega
  · rcases htcase with h0 | h1 | h2 | h3 | h4
    all_goals subst t
    ·
      omega
    ·
      omega
    ·
      omega
    ·
      omega
    ·
      omega
  · rcases htcase with h0 | h1 | h2 | h3 | h4
    all_goals subst t
    ·
      omega
    ·
      omega
    ·
      omega
    ·
      omega
    ·
      omega

/-- Finite state-list presentation for the original-source inverse lift. -/
def nodes (r : Nat) : List (Nat × Nat) :=
  [(0,8+32768*r),
   (1,13+49152*r),
   (2,16+57344*r),
   (3,11+36864*r),
   (3,18+61440*r),
   (4,11+34816*r),
   (4,16+51200*r),
   (5,13+39936*r),
   (5,19+58368*r),
   (6,18+52736*r),
   (6,21+61952*r),
   (7,14+39168*r),
   (7,21+59136*r),
   (8,17+45952*r),
   (8,23+62336*r)]

theorem mem_iff (r m z : Nat) : ((m,z) ∈ nodes r) ↔ State r m z := by
  simp only [nodes, State, List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false]

theorem nodes_root (r : Nat) : (0,32768*r+8) ∈ nodes r :=
  (mem_iff r 0 (32768*r+8)).mpr (state_root r)

theorem nodes_small (r m z : Nat) (h : (m,z) ∈ nodes r) : m ≤ 8 := by
  have hs := (mem_iff r m z).mp h
  rcases hs with ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩ | ⟨hm, hz⟩
  all_goals omega

theorem nodes_no256 (r m z : Nat) (h : (m,z) ∈ nodes r) : ¬256 ∣ z := by
  intro hd
  have hs := (mem_iff r m z).mp h
  have h32 : 32 ∣ z := Nat.dvd_trans (by decide : 32 ∣ 256) hd
  exact (state_nonzero_mod32 r m z hs) (Nat.mod_eq_zero_of_dvd h32)

theorem nodes_closed (r m z t v zp : Nat)
    (h : (m,z) ∈ nodes r) (hdiv : z = 2^t*v)
    (hnext : 2*zp+1 = 65536*r+19+m+t+v) :
    (m+t+1,zp) ∈ nodes r := by
  apply (mem_iff r (m+t+1) zp).mpr
  apply state_step r m z (m+t+1) zp ((mem_iff r m z).mp h)
  exact ⟨t,v,hdiv,rfl,hnext⟩

inductive Reach (r : Nat) : Nat → Nat → Prop where
  | root : Reach r 0 (32768*r+8)
  | extend (m z m' z' : Nat) : Reach r m z → Step r m z m' z' → Reach r m' z'

theorem reach_bound (r m z : Nat) (h : Reach r m z) : m≤8 := by
  have hs : State r m z := by
    induction h with
    | root => exact state_root r
    | extend m z m' z' _ he ih => exact state_step r m z m' z' ih he
  have hmem := (mem_iff r m z).mpr hs
  exact nodes_small r m z hmem

#print axioms nodes_closed
#print axioms reach_bound

#print axioms state_root
#print axioms state_step
end Agent23N14
