/-!
A triple-one block followed by isolated ones and separated by a
positive zero gap is fatal. All words here denote pair values, not bits.
-/
private theorem a12CR_triple_prepare (L R : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_CR_n_n ((1,0)::(1,0)::(1,0)::L) R)
      (cfg_EL_n_n ((0,0)::(0,0)::(3,0)::L) R) := by
  unfold cfg_CR_n_n cfg_EL_n_n
  simp only [encRight_d1_s0, encRight_d0_s0]
  rw [encRight_succ 2 0 L, encRight_succ 1 0 L, encRight_d1_s0 L]
  execute 25

private theorem a12DR_zero_pair (L R : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_DR_n_n ((0,0)::L) ((1,0)::R))
      (cfg_DR_n_n L ((1,0)::(0,0)::R)) := by
  unfold cfg_DR_n_n
  simp only [encRight_d0_s0, encLeft_d1_s0, encLeft_d0_s0]
  execute 4

private theorem a12DR_zero_sweep (n : ℕ) (L R : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_DR_n_n (List.replicate (n+1) (0,0) ++ L) ((1,0)::R))
      (cfg_DR_n_n L ((1,0)::(List.replicate (n+1) (0,0) ++ R))) := by
  induction n generalizing R with
  | zero => exact a12DR_zero_pair L R
  | succ n ih =>
    have h1 := a12DR_zero_pair (List.replicate (n+1) (0,0) ++ L) R
    have h2 := ih ((0,0)::R)
    rw [a12_rep_push (0,0) (n+1) R] at h2
    exact ReachesPlus.trans h1 h2

private theorem a12EL_barrier_high (n a : ℕ) (L R : List (ℕ × ℕ)) :
    ∃ c, ReachesPlus target
      (cfg_EL_n_n (List.replicate (n+1) (0,0) ++ (3,0)::L) ((a+3,0)::R)) c ∧
      (step target c).isNone := by
  let LL := List.replicate (n+1) (0,0) ++ (3,0)::L
  have h1 : ReachesPlus target (cfg_EL_n_n LL ((a+3,0)::R))
      (cfg_DR_n_n LL ((1,0)::(a,0)::R)) := by
    unfold cfg_EL_n_n cfg_DR_n_n
    rw [encLeft_succ (a+2) 0 R, encLeft_succ (a+1) 0 R,
      encLeft_succ a 0 R, encLeft_d1_s0]
    execute 5
  have h2 := a12DR_zero_sweep n ((3,0)::L) ((a,0)::R)
  let RR := List.replicate (n+1) (0,0) ++ (a,0)::R
  have h3 : ReachesPlus target (cfg_DR_n_n ((3,0)::L) ((1,0)::RR))
      (cfg_CR_n_n ((2,0)::L) ((0,0)::(0,0)::RR)) := by
    unfold cfg_DR_n_n cfg_CR_n_n
    rw [encRight_succ 2 0 L, encRight_succ 1 0 L, encRight_d1_s0 L,
      encLeft_d1_s0, encLeft_d0_s0, encLeft_d0_s0]
    execute 3
  obtain ⟨c,hc,hh⟩ := a12CR_high_halts 0 L ((0,0)::(0,0)::RR)
  exact ⟨c, ReachesPlus.trans h1 (ReachesPlus.trans h2 (ReachesPlus.trans h3 hc)), hh⟩

private theorem a12EL_barrier_two (n : ℕ) (L R : List (ℕ × ℕ)) :
    ∃ c, ReachesPlus target
      (cfg_EL_n_n (List.replicate (n+1) (0,0) ++ (3,0)::L) ((2,0)::R)) c ∧
      (step target c).isNone := by
  let LL := List.replicate (n+1) (0,0) ++ (3,0)::L
  have h1 : ReachesPlus target (cfg_EL_n_n LL ((2,0)::R))
      (tok_DR [2,0] R (LL.map Prod.fst)) := by
    unfold cfg_EL_n_n tok_DR
    rw [encLeft_succ 1 0 R, encLeft_d1_s0 R, encRight_eq_nat LL]
    texecute 5
  have hmap : LL.map Prod.fst = List.replicate (n+1) 0 ++ 3::L.map Prod.fst := by
    simp [LL, List.map_append, List.map_replicate]
  rw [hmap] at h1
  have h2 := a12_dr_sweep n [0] R (3::L.map Prod.fst)
  have h3 := tok_DR_succ (List.replicate (n+1) 1 ++ [0]) R 2 (L.map Prod.fst)
  obtain ⟨c,hc,hh⟩ := tok_CR_add2_halts
    (1::1::(List.replicate (n+1) 1 ++ [0])) R 0 (L.map Prod.fst)
  exact ⟨c, ReachesPlus.trans h1 (ReachesPlus.trans h2 (ReachesPlus.trans h3 hc)), hh⟩

private theorem a12EL_barrier_positive (n a : ℕ) (L R : List (ℕ × ℕ)) :
    ∃ c, ReachesPlus target
      (cfg_EL_n_n (List.replicate (n+1) (0,0) ++ (3,0)::L) ((a+2,0)::R)) c ∧
      (step target c).isNone := by
  cases a with
  | zero => exact a12EL_barrier_two n L R
  | succ a => exact a12EL_barrier_high n a L R

private theorem a12CR_triple_zeros_high (n a : ℕ) (L R : List (ℕ × ℕ)) :
    ∃ c, ReachesPlus target
      (cfg_CR_n_n ((1,0)::(1,0)::(1,0)::L)
        (List.replicate (n+1) (0,0) ++ (a+2,0)::R)) c ∧
      (step target c).isNone := by
  have h1 := a12CR_triple_prepare L (List.replicate (n+1) (0,0) ++ (a+2,0)::R)
  have h2 := a12EL_sweep n ((0,0)::(0,0)::(3,0)::L) ((a+2,0)::R)
  rw [a12_rep_push (0,0) (n+1) ((0,0)::(3,0)::L),
      a12_rep_push (0,0) (n+2) ((3,0)::L)] at h2
  obtain ⟨c,hc,hh⟩ := a12EL_barrier_positive (n+2) a L R
  exact ⟨c, ReachesPlus.trans h1 (ReachesPlus.trans h2 hc), hh⟩

private theorem a12CR_triple_zero_high (a : ℕ) (L R : List (ℕ × ℕ)) :
    ∃ c, ReachesPlus target
      (cfg_CR_n_n ((1,0)::(1,0)::(1,0)::L) ((0,0)::(a+2,0)::R)) c ∧
      (step target c).isNone := a12CR_triple_zeros_high 0 a L R

#print axioms a12CR_triple_zeros_high

private theorem a12CR_one_zero_pair (b : ℕ) (L R : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_CR_n_n ((1,0)::(0,0)::L) ((b,0)::R))
      (cfg_CR_n_n L ((0,0)::(b+3,0)::R)) := by
  unfold cfg_CR_n_n
  simp only [encRight_d1_s0, encRight_d0_s0, encLeft_d0_s0]
  rw [encLeft_succ (b+2) 0 R, encLeft_succ (b+1) 0 R, encLeft_succ b 0 R]
  execute 5

inductive a12Collectable : List (ℕ × ℕ) → Prop
  | nil : a12Collectable []
  | zero {P} : a12Collectable P → a12Collectable ((0,0)::P)
  | oneZero {P} : a12Collectable P → a12Collectable ((1,0)::(0,0)::P)

def a12HighRight (R : List (ℕ × ℕ)) : Prop :=
  (∃ a T, R = (a+2,0)::T) ∨ (∃ a T, R = (0,0)::(a+2,0)::T)

theorem a12CR_collectable_triple_halts (P : List (ℕ × ℕ)) (hp : a12Collectable P)
    (L R : List (ℕ × ℕ)) (hr : a12HighRight R) :
    ∃ c, ReachesPlus target
      (cfg_CR_n_n (P ++ (1,0)::(1,0)::(1,0)::L) R) c ∧
      (step target c).isNone := by
  induction hp generalizing R with
  | nil =>
    rcases hr with ⟨a,T,rfl⟩ | ⟨a,T,rfl⟩
    · exact a12CR_triple_positive a L T
    · exact a12CR_triple_zero_high a L T
  | @zero P hP ih =>
    let LL := P ++ (1,0)::(1,0)::(1,0)::L
    rcases hr with ⟨a,T,rfl⟩ | ⟨a,T,rfl⟩
    · have h := a12CR_zero_pair (a+2) LL T
      obtain ⟨c,hc,hh⟩ := ih ((a+2+2,0)::T) (Or.inl ⟨a+2,T,rfl⟩)
      exact ⟨c,ReachesPlus.trans h hc,hh⟩
    · have h := a12CR_zero_pair 0 LL ((a+2,0)::T)
      obtain ⟨c,hc,hh⟩ := ih ((2,0)::(a+2,0)::T) (Or.inl ⟨0,_,rfl⟩)
      exact ⟨c,ReachesPlus.trans h hc,hh⟩
  | @oneZero P hP ih =>
    let LL := P ++ (1,0)::(1,0)::(1,0)::L
    rcases hr with ⟨a,T,rfl⟩ | ⟨a,T,rfl⟩
    · have h := a12CR_one_zero_pair (a+2) LL T
      obtain ⟨c,hc,hh⟩ := ih ((0,0)::(a+2+3,0)::T) (Or.inr ⟨a+3,T,by
        have he : a+2+3 = a+3+2 := by omega
        rw [he]⟩)
      exact ⟨c,ReachesPlus.trans h hc,hh⟩
    · have h := a12CR_one_zero_pair 0 LL ((a+2,0)::T)
      obtain ⟨c,hc,hh⟩ := ih ((0,0)::(3,0)::(a+2,0)::T) (Or.inr ⟨1,_,rfl⟩)
      exact ⟨c,ReachesPlus.trans h hc,hh⟩

#print axioms a12CR_collectable_triple_halts

private theorem a12Binary_append (v w : List Bool) :
    a12Binary (v ++ w) = a12Binary v ++ a12Binary w := by
  simp [a12Binary]

private theorem a12EL_scan_binary (v : List Bool) (L R : List (ℕ × ℕ)) :
    v = [] ∨ ReachesPlus target
      (cfg_EL_n_n ((0,0)::L) (a12Binary v ++ R))
      (cfg_EL_n_n ((0,0)::(a12Binary v.reverse ++ L)) R) := by
  induction v generalizing L with
  | nil => exact Or.inl rfl
  | cons b v ih =>
    cases b
    · have h1 := a12EL_zero ((0,0)::L) (a12Binary v ++ R)
      rcases ih ((0,0)::L) with rfl | h2
      · exact Or.inr h1
      · right
        have h := ReachesPlus.trans h1 h2
        simpa [List.reverse_cons, a12Binary_append, a12Binary,
          List.append_assoc] using h
    · have h1 := a12EL_one L (a12Binary v ++ R)
      rcases ih ((1,0)::L) with rfl | h2
      · exact Or.inr h1
      · right
        have h := ReachesPlus.trans h1 h2
        simpa [List.reverse_cons, a12Binary_append, a12Binary,
          List.append_assoc] using h

theorem a12EL_triple_collectable_tail_halts (v : List Bool)
    (hv : a12Collectable (a12Binary v.reverse)) (L : List (ℕ × ℕ)) :
    ∃ c, ReachesPlus target
      (cfg_EL_n_n ((0,0)::L) ([(1,0),(1,0),(1,0)] ++ a12Binary v)) c ∧
      (step target c).isNone := by
  let P := a12Binary v.reverse
  let LL := P ++ (1,0)::(1,0)::(1,0)::L
  rcases a12EL_scan_binary ([true,true,true] ++ v) L [] with he | h1
  · simp at he
  have h1' : ReachesPlus target
      (cfg_EL_n_n ((0,0)::L) ([(1,0),(1,0),(1,0)] ++ a12Binary v))
      (cfg_EL_n_n ((0,0)::LL) []) := by
    simpa [LL, P, a12Binary_append, List.reverse_append, a12Binary,
      List.append_assoc] using h1
  have h2 := a12EL_empty ((0,0)::LL)
  have h3 := a12CR_zero_pair 0 LL []
  obtain ⟨c,hc,hh⟩ := a12CR_collectable_triple_halts P hv L [(2,0)]
    (Or.inl ⟨0,[],rfl⟩)
  exact ⟨c,ReachesPlus.trans h1' (ReachesPlus.trans h2 (ReachesPlus.trans h3 hc)),hh⟩

theorem a12G_binary_111_collectable_tail_halts (k : ℕ) (w v : List Bool)
    (hv : a12Collectable (a12Binary v.reverse)) :
    ∃ c, ReachesPlus target
      (cfg_CR_n_n [(0,0)] (List.replicate (k+1) (0,0) ++
        (a12Binary w ++ ([(1,0),(1,0),(1,0)] ++ a12Binary v)))) c ∧
      (step target c).isNone := by
  let S := [(1,0),(1,0),(1,0)] ++ a12Binary v
  have h := a12G_to_EL k (a12Binary w ++ S)
  obtain ⟨c,hc,hh⟩ := a12EL_prefix_halts S
    (a12EL_triple_collectable_tail_halts v hv) w
    (List.replicate (k+2) (0,0) ++ [(1,0)])
  exact ⟨c,ReachesPlus.trans h hc,hh⟩

#print axioms a12G_binary_111_collectable_tail_halts
