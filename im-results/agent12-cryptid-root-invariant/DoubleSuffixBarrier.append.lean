/-!
A unified token-mode halting barrier for arbitrary strings of blocks 0, 10,
and 1100 before a terminal 111 on the CR stack. Append after
TokenCounterCorrection.append.lean in the pinned original source namespace.
No dependency on the earlier (partly failing) suffix append files.
-/

inductive a12DoubleCollectable : List ℕ → Prop
  | nil : a12DoubleCollectable []
  | zero {P} : a12DoubleCollectable P → a12DoubleCollectable (0::P)
  | oneZero {P} : a12DoubleCollectable P → a12DoubleCollectable (1::0::P)
  | doubleZero {P} : a12DoubleCollectable P → a12DoubleCollectable (1::1::0::0::P)

private inductive A12TokenHigh : List ℕ → Prop
  | high (a : ℕ) (T : List ℕ) : A12TokenHigh ((a+3)::T)
  | oneHigh (a : ℕ) (T : List ℕ) : A12TokenHigh (1::(a+3)::T)

-- The key uniform reduction: two leading ones are removed, and the next
-- digit is increased by one. The right tail and the left tail are untouched.
private theorem a12ExposeDouble (a c : ℕ) (T : List ℕ)
    (W : List (ℕ × ℕ)) (L : List ℕ) :
    ReachesPlus target (tok_CR ((a+3)::T) W (1::1::c::L))
      (tok_CR (1::1::1::1::a::T) W ((c+1)::L)) := by
  have h1 := tok_CR_1_1_cons_25 (a+3) T W c L
  have h2 := tok_EL_add3 a T W (0::0::(c+2)::L)
  have h3 := tok_DR_zero (a::T) W (0::(c+2)::L)
  have h4 := tok_DR_zero (1::a::T) W ((c+2)::L)
  have h5 := tok_DR_succ (1::1::a::T) W (c+1) L
  exact ReachesPlus.trans h1 (ReachesPlus.trans h2
    (ReachesPlus.trans h3 (ReachesPlus.trans h4 h5)))

private theorem a12ExposeDoubleOne (a c : ℕ) (T : List ℕ)
    (W : List (ℕ × ℕ)) (L : List ℕ) :
    ReachesPlus target (tok_CR (1::(a+3)::T) W (1::1::c::L))
      (tok_CR (1::1::1::1::1::a::T) W ((c+1)::L)) := by
  have h1 := tok_CR_1_1_cons_25 1 ((a+3)::T) W c L
  have h2 := tok_EL_1 ((a+3)::T) W (0::0::(c+2)::L)
  have h3 := tok_EL_add3 a T W (0::0::0::(c+2)::L)
  have h4 := tok_DR_zero (a::T) W (0::0::(c+2)::L)
  have h5 := tok_DR_zero (1::a::T) W (0::(c+2)::L)
  have h6 := tok_DR_zero (1::1::a::T) W ((c+2)::L)
  have h7 := tok_DR_succ (1::1::1::a::T) W (c+1) L
  exact ReachesPlus.trans h1 (ReachesPlus.trans h2
    (ReachesPlus.trans h3 (ReachesPlus.trans h4
      (ReachesPlus.trans h5 (ReachesPlus.trans h6 h7)))))

private theorem a12High_zero (K : List ℕ) (hk : A12TokenHigh K)
    (W : List (ℕ × ℕ)) (L : List ℕ) :
    ∃ K', A12TokenHigh K' ∧
      ReachesPlus target (tok_CR K W (0::L)) (tok_CR K' W L) := by
  cases hk with
  | high a T =>
    exact ⟨(a+5)::T, .high (a+2) T, tok_CR_zero (a+3) T W L⟩
  | oneHigh a T =>
    exact ⟨3::(a+3)::T, .high 0 ((a+3)::T),
      tok_CR_zero 1 ((a+3)::T) W L⟩

private theorem a12High_oneZero (K : List ℕ) (hk : A12TokenHigh K)
    (W : List (ℕ × ℕ)) (L : List ℕ) :
    ∃ K', A12TokenHigh K' ∧
      ReachesPlus target (tok_CR K W (1::0::L)) (tok_CR K' W L) := by
  cases hk with
  | high a T =>
    exact ⟨1::(a+6)::T, .oneHigh (a+3) T, tok_CR_1_0 (a+3) T W L⟩
  | oneHigh a T =>
    exact ⟨1::4::(a+3)::T, .oneHigh 1 ((a+3)::T),
      tok_CR_1_0 1 ((a+3)::T) W L⟩

private theorem a12High_doubleZero (K : List ℕ) (hk : A12TokenHigh K)
    (W : List (ℕ × ℕ)) (L : List ℕ) :
    ∃ K', A12TokenHigh K' ∧
      ReachesPlus target (tok_CR K W (1::1::0::0::L)) (tok_CR K' W L) := by
  cases hk with
  | high a T =>
    have h1 := a12ExposeDouble a 0 T W (0::L)
    have h2 := tok_CR_1_0 1 (1::1::1::a::T) W L
    exact ⟨1::4::1::1::1::a::T, .oneHigh 1 (1::1::1::a::T),
      ReachesPlus.trans h1 h2⟩
  | oneHigh a T =>
    have h1 := a12ExposeDoubleOne a 0 T W (0::L)
    have h2 := tok_CR_1_0 1 (1::1::1::1::a::T) W L
    exact ⟨1::4::1::1::1::1::a::T, .oneHigh 1 (1::1::1::1::a::T),
      ReachesPlus.trans h1 h2⟩

private theorem a12High_triple (K : List ℕ) (hk : A12TokenHigh K)
    (W : List (ℕ × ℕ)) (L : List ℕ) :
    ∃ c, ReachesPlus target (tok_CR K W (1::1::1::L)) c ∧
      (step target c).isNone := by
  cases hk with
  | high a T =>
    have h1 := a12ExposeDouble a 1 T W L
    obtain ⟨c,hc,hh⟩ := tok_CR_add2_halts (1::1::1::1::a::T) W 0 L
    exact ⟨c, ReachesPlus.trans h1 hc, hh⟩
  | oneHigh a T =>
    have h1 := a12ExposeDoubleOne a 1 T W L
    obtain ⟨c,hc,hh⟩ := tok_CR_add2_halts (1::1::1::1::1::a::T) W 0 L
    exact ⟨c, ReachesPlus.trans h1 hc, hh⟩

private theorem a12Token_double_barrier (P : List ℕ) (hp : a12DoubleCollectable P)
    (K : List ℕ) (hk : A12TokenHigh K) (W : List (ℕ × ℕ)) (L : List ℕ) :
    ∃ c, ReachesPlus target (tok_CR K W (P ++ 1::1::1::L)) c ∧
      (step target c).isNone := by
  induction hp generalizing K with
  | nil => exact a12High_triple K hk W L
  | @zero P hp ih =>
    obtain ⟨K',hk',h⟩ := a12High_zero K hk W (P ++ 1::1::1::L)
    obtain ⟨c,hc,hh⟩ := ih K' hk'
    exact ⟨c, ReachesPlus.trans h hc, hh⟩
  | @oneZero P hp ih =>
    obtain ⟨K',hk',h⟩ := a12High_oneZero K hk W (P ++ 1::1::1::L)
    obtain ⟨c,hc,hh⟩ := ih K' hk'
    exact ⟨c, ReachesPlus.trans h hc, hh⟩
  | @doubleZero P hp ih =>
    obtain ⟨K',hk',h⟩ := a12High_doubleZero K hk W (P ++ 1::1::1::L)
    obtain ⟨c,hc,hh⟩ := ih K' hk'
    exact ⟨c, ReachesPlus.trans h hc, hh⟩

-- Ordinary pairs and tokens are two encodings of the same tape.
-- The final two zero tokens are padding on the blank tail.
private theorem a12Tokens_pairs (R : List (ℕ × ℕ)) :
    encTokens (R.map (fun p => p.1+1) ++ [0,0]) [] = encLeft R := by
  induction R with
  | nil =>
    simp only [List.map_nil, List.nil_append, encTokens_zero, encTokens_nil,
      encLeft_nil, ListBlank.cons_zero_default]
  | cons p R ih =>
    rcases p with ⟨a,b⟩
    simp only [List.map_cons, List.cons_append, Prod.fst, encTokens, encLeft_cons,
      Nat.one_mul, Nat.mod_one, Nat.add_zero, list_pow_succ, list_pow_zero,
      List.cons_append, List.nil_append, ListBlank.append_cons, ListBlank.append_nil]
    rw [ih]

def a12WordPairs (w : List Bool) : List (ℕ × ℕ) :=
  w.map fun b => (if b then 1 else 0,0)

def a12WordNat (w : List Bool) : List ℕ :=
  w.map fun b => if b then 1 else 0

private def a12WordTokens (w : List Bool) : List ℕ :=
  (a12WordPairs w).map fun p => p.1+1

-- Collect a binary word, then enter CR with a single high token 3.
private theorem a12Collect_binary_tokens (w : List Bool) (L : List ℕ) :
    ReachesPlus target (tok_EL (a12WordTokens w ++ [0,0]) [] (0::L))
      (tok_CR [3] [] (a12WordNat w.reverse ++ L)) := by
  induction w generalizing L with
  | nil =>
    have h1 := tok_EL_0_cons 0 [] [] (0::L)
    have h2 := tok_CR_zero 1 [] [] L
    simpa [a12WordTokens, a12WordPairs, a12WordNat] using ReachesPlus.trans h1 h2
  | cons b w ih =>
    cases b
    · have h := tok_EL_1 (a12WordTokens w ++ [0,0]) [] (0::L)
      have hs := ih (0::L)
      simpa [a12WordTokens, a12WordPairs, a12WordNat, List.reverse_cons,
        List.map_append, List.append_assoc] using ReachesPlus.trans h hs
    · have h := tok_EL_2 (a12WordTokens w ++ [0,0]) [] L
      have hs := ih (1::L)
      simpa [a12WordTokens, a12WordPairs, a12WordNat, List.reverse_cons,
        List.map_append, List.append_assoc] using ReachesPlus.trans h hs

/-- All binary suffixes w111v, where reverse(v) is in (0|10|1100)*,
are halting prepared G configurations. This is not a blank-root claim. -/
theorem a12G_double_suffix_halts (k : ℕ) (w v : List Bool)
    (hv : a12DoubleCollectable (a12WordNat v.reverse)) :
    ∃ c, ReachesPlus target
      (cfg_CR_n_n [(0,0)] (List.replicate (k+1) (0,0) ++
        a12WordPairs (w ++ [true,true,true] ++ v))) c ∧ (step target c).isNone := by
  let u := w ++ [true,true,true] ++ v
  let K := a12WordTokens u ++ [0,0]
  have he : cfg_CR_n_n [(0,0)] (List.replicate (k+1) (0,0) ++ a12WordPairs u) =
      tok_CR (List.replicate (k+1) 1 ++ K) [] [0] := by
    unfold cfg_CR_n_n tok_CR
    rw [encRight_eq_nat, ← a12Tokens_pairs
      (List.replicate (k+1) (0,0) ++ a12WordPairs u)]
    simp [K, a12WordTokens, List.map_append, List.map_replicate, List.append_assoc]
  have h1 := tok_CR_zero 1 (List.replicate k 1 ++ K) [] []
  have h2 := tok_CR_add2_nil_21 1 (List.replicate k 1 ++ K) []
  have h3 := a12_el_sweep k K [] [0,0,1]
  have h4 := a12Collect_binary_tokens u (List.replicate k 0 ++ [0,0,1])
  have h : ReachesPlus target (tok_CR (List.replicate (k+1) 1 ++ K) [] [0])
      (tok_CR [3] [] (a12WordNat u.reverse ++ (List.replicate k 0 ++ [0,0,1]))) := by
    exact ReachesPlus.trans h1 (ReachesPlus.trans h2 (ReachesPlus.trans h3 h4))
  obtain ⟨c,hc,hh⟩ := a12Token_double_barrier
    (a12WordNat v.reverse) hv [3] (.high 0 []) []
    (a12WordNat w.reverse ++ (List.replicate k 0 ++ [0,0,1]))
  have h' : ReachesPlus target
      (cfg_CR_n_n [(0,0)] (List.replicate (k+1) (0,0) ++ a12WordPairs u))
      (tok_CR [3] [] (a12WordNat v.reverse ++ 1::1::1::
        (a12WordNat w.reverse ++ (List.replicate k 0 ++ [0,0,1])))) := by
    rw [he]
    simpa [u, a12WordNat, List.reverse_append, List.map_append,
      List.append_assoc] using h
  exact ⟨c, ReachesPlus.trans h' hc, hh⟩

#print axioms a12ExposeDouble
#print axioms a12ExposeDoubleOne
#print axioms a12Token_double_barrier
#print axioms a12G_double_suffix_halts
