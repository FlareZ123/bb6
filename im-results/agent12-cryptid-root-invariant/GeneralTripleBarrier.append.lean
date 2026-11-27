/-!
All binary triple-containing left words halt from a good token stack.
Append after TokenCounterCorrection and DoubleSuffixBarrier, which have
a source-accepted full closure (run 46041206114). See GeneralTripleBarrier.md.
-/

private inductive A12Pairable : List ℕ → Prop
  | nil : A12Pairable []
  | other {k : ℕ} {T : List ℕ} (hk : k ≠ 2) :
      A12Pairable T → A12Pairable (k::T)
  | pair {T : List ℕ} : A12Pairable T → A12Pairable (1::2::T)
  -- Zero is a protected cut: no pairing condition beyond it.
  | cut (T : List ℕ) : A12Pairable (0::T)

private inductive A12Good : List ℕ → Prop
  | mk {k : ℕ} {T : List ℕ} (hk : 0 < k) (hne : k ≠ 2)
      (hT : A12Pairable T) : A12Good (k::T)

private inductive A12Collect : List ℕ → Prop
  | nil : A12Collect []
  | zero {P : List ℕ} : A12Collect P → A12Collect (0::P)
  | oneZero {P : List ℕ} : A12Collect P → A12Collect (1::0::P)

private theorem a12Collect_append {P Q : List ℕ} (hP : A12Collect P)
    (hQ : A12Collect Q) : A12Collect (P ++ Q) := by
  induction hP with
  | nil => exact hQ
  | zero h ih => exact .zero ih
  | oneZero h ih => exact .oneZero ih

-- B is scanned left-to-right in blocks 1 or 12, P is its collected
-- reverse word with token values decremented by one.
private inductive A12Scan : List ℕ → List ℕ → Prop
  | nil : A12Scan [] []
  | one {B P : List ℕ} : A12Scan B P → A12Scan (1::B) (P ++ [0])
  | pair {B P : List ℕ} : A12Scan B P → A12Scan (1::2::B) (P ++ [1,0])

private theorem a12Scan_collect {B P : List ℕ} (h : A12Scan B P) :
    A12Collect P := by
  induction h with
  | nil => exact .nil
  | one h ih => exact a12Collect_append ih (.zero .nil)
  | pair h ih => exact a12Collect_append ih (.oneZero .nil)

private inductive A12Stop : List ℕ → Prop
  | nil : A12Stop []
  | zero (T : List ℕ) : A12Stop (0::T)
  | high (a : ℕ) (T : List ℕ) (hT : A12Pairable T) :
      A12Stop ((a+3)::T)

private theorem a12Paired_split (X : List ℕ) (hX : A12Pairable X) :
    ∃ B P T, A12Scan B P ∧ A12Stop T ∧ X = B ++ T := by
  induction hX with
  | nil => exact ⟨[],[],[],.nil,.nil,rfl⟩
  | @other k T hk hT ih =>
    cases k with
    | zero => exact ⟨[],[],0::T,.nil,.zero T,rfl⟩
    | succ k =>
      cases k with
      | zero =>
        obtain ⟨B,P,S,hB,hS,he⟩ := ih
        exact ⟨1::B,P++[0],S,.one hB,hS,by rw [he]; rfl⟩
      | succ k =>
        cases k with
        | zero => exact (hk rfl).elim
        | succ k => exact ⟨[],[],(k+3)::T,.nil,.high k T hT,rfl⟩
  | @pair T hT ih =>
    obtain ⟨B,P,S,hB,hS,he⟩ := ih
    exact ⟨1::2::B,P++[1,0],S,.pair hB,hS,by rw [he]; rfl⟩
  | cut T => exact ⟨[],[],0::T,.nil,.zero T,rfl⟩

-- Either B was all ones, or the collected P contains a first 10 block.
private theorem a12Scan_cases {B P : List ℕ} (h : A12Scan B P) :
    (∃ d : ℕ, B = List.replicate d 1 ∧ P = List.replicate d 0) ∨
    (∃ z Q, P = List.replicate z 0 ++ 1::0::Q ∧ A12Collect Q) := by
  induction h with
  | nil => exact Or.inl ⟨0,rfl,rfl⟩
  | @one B P h ih =>
    rcases ih with ⟨d,hB,hP⟩ | ⟨z,Q,hP,hQ⟩
    · left
      refine ⟨d+1,by rw [hB]; rfl,?_⟩
      rw [hP, a12_rep_add (0:ℕ) d 1]
      rfl
    · right
      exact ⟨z,Q++[0],by rw [hP]; simp [List.append_assoc],
        a12Collect_append hQ (.zero .nil)⟩
  | @pair B P h ih =>
    rcases ih with ⟨d,hB,hP⟩ | ⟨z,Q,hP,hQ⟩
    · right
      exact ⟨d,[],by rw [hP],.nil⟩
    · right
      exact ⟨z,Q++[1,0],by rw [hP]; simp [List.append_assoc],
        a12Collect_append hQ (.oneZero .nil)⟩

-- Scan a paired binary prefix, composing with its terminal continuation.
private theorem a12Scan_continue {B P : List ℕ} (h : A12Scan B P)
    (K : List ℕ) (W : List (ℕ × ℕ)) (L : List ℕ)
    (hh : ∃ c, ReachesPlus target (tok_EL K W (0::P++L)) c ∧
      (step target c).isNone) :
    ∃ c, ReachesPlus target (tok_EL (B++K) W (0::L)) c ∧
      (step target c).isNone := by
  induction h generalizing L with
  | nil => exact hh
  | @one B P h ih =>
    obtain ⟨c,hc,hhalt⟩ := ih (0::L) (by
      simpa [List.append_assoc] using hh)
    have h1 := tok_EL_1 (B++K) W (0::L)
    exact ⟨c,ReachesPlus.trans h1 hc,hhalt⟩
  | @pair B P h ih =>
    obtain ⟨c,hc,hhalt⟩ := ih (1::0::L) (by
      simpa [List.append_assoc] using hh)
    have h1 := tok_EL_1 (2::B++K) W (0::L)
    have h2 := tok_EL_2 (B++K) W (0::L)
    exact ⟨c,ReachesPlus.trans h1 (ReachesPlus.trans h2 hc),hhalt⟩

-- A collectable left prefix before a high marker is fatal for any
-- nonempty token stack, not merely a good stack.
private theorem a12Collect_high {P : List ℕ} (hP : A12Collect P)
    (k : ℕ) (K : List ℕ) (W : List (ℕ × ℕ)) (c : ℕ) (L : List ℕ) :
    ∃ q, ReachesPlus target (tok_CR (k::K) W (P++(c+2)::L)) q ∧
      (step target q).isNone := by
  induction hP generalizing k K with
  | nil => exact tok_CR_add2_halts (k::K) W c L
  | @zero P hP ih =>
    have h1 := tok_CR_zero k K W (P++(c+2)::L)
    obtain ⟨q,hq,hh⟩ := ih (k+2) K
    exact ⟨q,ReachesPlus.trans h1 hq,hh⟩
  | @oneZero P hP ih =>
    have h1 := tok_CR_1_0 k K W (P++(c+2)::L)
    obtain ⟨q,hq,hh⟩ := ih 1 ((k+3)::K)
    exact ⟨q,ReachesPlus.trans h1 hq,hh⟩

private theorem a12Scan_zero_fatal {B P : List ℕ} (h : A12Scan B P)
    (k : ℕ) (K : List ℕ) (W : List (ℕ × ℕ)) (c : ℕ) (L : List ℕ) :
    ∃ q, ReachesPlus target
      (tok_EL (B++0::k::K) W (0::0::(c+2)::L)) q ∧
      (step target q).isNone := by
  have hp := a12Collect_append (.zero (a12Scan_collect h)) (.zero .nil)
  obtain ⟨q,hq,hh⟩ := a12Collect_high hp (k+1) K W c L
  have h1 := tok_EL_0_cons k K W (0::P++0::(c+2)::L)
  have hq' : ReachesPlus target
      (tok_CR ((k+1)::K) W (0::P++0::(c+2)::L)) q := by
    simpa [List.append_assoc] using hq
  exact a12Scan_continue h (0::k::K) W (0::(c+2)::L)
    ⟨q,ReachesPlus.trans h1 hq',hh⟩

private theorem a12Scan_high_fatal {B P : List ℕ} (h : A12Scan B P)
    (z : ℕ) (Q : List ℕ) (hP : P = List.replicate z 0 ++ 1::0::Q)
    (hQ : A12Collect Q) (a : ℕ) (T : List ℕ) (W : List (ℕ × ℕ))
    (c : ℕ) (L : List ℕ) :
    ∃ q, ReachesPlus target
      (tok_EL (B++(a+3)::T) W (0::0::(c+2)::L)) q ∧
      (step target q).isNone := by
  let LL := 0::Q++0::(c+2)::L
  have h1 := tok_EL_add3 a T W (List.replicate (z+1) 0 ++ 1::LL)
  have h2 := a12_dr_sweep z (a::T) W (1::LL)
  have h3 := tok_DR_succ (List.replicate (z+1) 1 ++ a::T) W 0 LL
  have hp := a12Collect_append (.zero (.zero hQ)) (.zero .nil)
  obtain ⟨q,hq,hh⟩ := a12Collect_high hp 1
    (1::List.replicate (z+1) 1 ++ a::T) W c L
  have hq' : ReachesPlus target
      (tok_CR (1::1::List.replicate (z+1) 1 ++ a::T) W (0::LL)) q := by
    simpa [LL,List.append_assoc] using hq
  have he := ReachesPlus.trans h1 (ReachesPlus.trans h2 (ReachesPlus.trans h3 hq'))
  have he' : ReachesPlus target
      (tok_EL ((a+3)::T) W (0::P++0::(c+2)::L)) q := by
    simpa [hP,LL,List.replicate_succ,List.append_assoc] using he
  exact a12Scan_continue h ((a+3)::T) W (0::(c+2)::L) ⟨q,he',hh⟩

private theorem a12ExposeDoubleMany (d a c : ℕ) (T : List ℕ)
    (W : List (ℕ × ℕ)) (L : List ℕ) :
    ReachesPlus target
      (tok_CR (List.replicate d 1 ++ (a+3)::T) W (1::1::c::L))
      (tok_CR (List.replicate (d+4) 1 ++ a::T) W ((c+1)::L)) := by
  cases d with
  | zero => exact a12ExposeDouble a c T W L
  | succ d =>
    have h1 := tok_CR_1_1_cons_25 1
      (List.replicate d 1 ++ (a+3)::T) W c L
    have h2 := a12_el_sweep d ((a+3)::T) W (0::0::(c+2)::L)
    rw [a12_rep_push 0 (d+1) (0::(c+2)::L),
        a12_rep_push 0 (d+2) ((c+2)::L)] at h2
    have h3 := tok_EL_add3 a T W (List.replicate (d+3) 0 ++ (c+2)::L)
    have h4 := a12_dr_sweep (d+2) (a::T) W ((c+2)::L)
    have h5 := tok_DR_succ (List.replicate (d+3) 1 ++ a::T) W (c+1) L
    exact ReachesPlus.trans h1 (ReachesPlus.trans h2
      (ReachesPlus.trans h3 (ReachesPlus.trans h4 h5)))

private theorem a12Pairable_ones (d : ℕ) (T : List ℕ) (hT : A12Pairable T) :
    A12Pairable (List.replicate d 1 ++ T) := by
  induction d with
  | zero => exact hT
  | succ d ih => exact .other (by decide) ih

private theorem a12Good_double_tail (d a : ℕ) (T : List ℕ) (hT : A12Pairable T) :
    A12Good (List.replicate (d+4) 1 ++ a::T) := by
  have hPair : A12Pairable (1::a::T) := by
    by_cases ha : a=2
    · subst a
      exact .pair hT
    · exact .other (by decide) (.other ha hT)
  have hTail := a12Pairable_ones (d+2) (1::a::T) hPair
  rw [a12_rep_push 1 (d+2) (a::T)] at hTail
  exact .mk (by decide) (by decide) hTail

private theorem a12Good_zero (X : List ℕ) (hx : A12Good X)
    (W : List (ℕ × ℕ)) (L : List ℕ) :
    ∃ X', A12Good X' ∧ ReachesPlus target
      (tok_CR (X++[0,0]) W (0::L)) (tok_CR (X'++[0,0]) W L) := by
  cases hx with
  | @mk k T hk hn hT =>
    refine ⟨(k+2)::T,.mk (by omega) (by omega) hT,?_⟩
    simpa only [List.cons_append] using tok_CR_zero k (T++[0,0]) W L

private theorem a12Good_oneZero (X : List ℕ) (hx : A12Good X)
    (W : List (ℕ × ℕ)) (L : List ℕ) :
    ∃ X', A12Good X' ∧ ReachesPlus target
      (tok_CR (X++[0,0]) W (1::0::L)) (tok_CR (X'++[0,0]) W L) := by
  cases hx with
  | @mk k T hk hn hT =>
    refine ⟨1::(k+3)::T,.mk (by decide) (by decide) (.other (by omega) hT),?_⟩
    simpa only [List.cons_append] using tok_CR_1_0 k (T++[0,0]) W L

private theorem a12Good_startDouble (X : List ℕ) (hx : A12Good X)
    (W : List (ℕ × ℕ)) (c : ℕ) (L : List ℕ) :
    ReachesPlus target (tok_CR (X++[0,0]) W (1::1::c::L))
      (tok_EL (X++[0,0]) W (0::0::(c+2)::L)) := by
  cases hx with
  | @mk k T hk hn hT => exact tok_CR_1_1_cons_25 k (T++[0,0]) W c L

private theorem a12Good_pairable (X : List ℕ) (hx : A12Good X) : A12Pairable X := by
  cases hx with
  | @mk k T hk hn hT => exact .other hn hT

private theorem a12Good_double (X : List ℕ) (hx : A12Good X)
    (W : List (ℕ × ℕ)) (c : ℕ) (L : List ℕ) :
    (∃ q, ReachesPlus target (tok_CR (X++[0,0]) W (1::1::c::L)) q ∧
      (step target q).isNone) ∨
    (∃ X', A12Good X' ∧ ReachesPlus target
      (tok_CR (X++[0,0]) W (1::1::c::L))
      (tok_CR (X'++[0,0]) W ((c+1)::L))) := by
  have h0 := a12Good_startDouble X hx W c L
  obtain ⟨B,P,T,hS,hT,hX⟩ := a12Paired_split X (a12Good_pairable X hx)
  cases hT with
  | nil =>
    obtain ⟨q,hq,hh⟩ := a12Scan_zero_fatal hS 0 [] W c L
    have hq' : ReachesPlus target
        (tok_EL (X++[0,0]) W (0::0::(c+2)::L)) q := by
      simpa [hX,List.append_assoc] using hq
    exact Or.inl ⟨q,ReachesPlus.trans h0 hq',hh⟩
  | zero T =>
    cases T with
    | nil =>
      obtain ⟨q,hq,hh⟩ := a12Scan_zero_fatal hS 0 [0] W c L
      have hq' : ReachesPlus target
          (tok_EL (X++[0,0]) W (0::0::(c+2)::L)) q := by
        simpa [hX,List.append_assoc] using hq
      exact Or.inl ⟨q,ReachesPlus.trans h0 hq',hh⟩
    | cons k T =>
      obtain ⟨q,hq,hh⟩ := a12Scan_zero_fatal hS k (T++[0,0]) W c L
      have hq' : ReachesPlus target
          (tok_EL (X++[0,0]) W (0::0::(c+2)::L)) q := by
        simpa [hX,List.append_assoc] using hq
      exact Or.inl ⟨q,ReachesPlus.trans h0 hq',hh⟩
  | high a T hT =>
    rcases a12Scan_cases hS with ⟨d,hB,hP⟩ | ⟨z,Q,hP,hQ⟩
    · right
      refine ⟨List.replicate (d+4) 1 ++ a::T,a12Good_double_tail d a T hT,?_⟩
      simpa [hX,hB,List.append_assoc] using
        a12ExposeDoubleMany d a c (T++[0,0]) W L
    · obtain ⟨q,hq,hh⟩ := a12Scan_high_fatal hS z Q hP hQ a (T++[0,0]) W c L
      have hq' : ReachesPlus target
          (tok_EL (X++[0,0]) W (0::0::(c+2)::L)) q := by
        simpa [hX,List.append_assoc] using hq
      exact Or.inl ⟨q,ReachesPlus.trans h0 hq',hh⟩

private theorem a12Good_triple (X : List ℕ) (hx : A12Good X)
    (W : List (ℕ × ℕ)) (L : List ℕ) :
    ∃ q, ReachesPlus target (tok_CR (X++[0,0]) W (1::1::1::L)) q ∧
      (step target q).isNone := by
  rcases a12Good_double X hx W 1 L with hh | ⟨X',hX',h⟩
  · exact hh
  · obtain ⟨q,hq,hh⟩ := tok_CR_add2_halts (X'++[0,0]) W 0 L
    exact ⟨q,ReachesPlus.trans h hq,hh⟩

-- Arbitrary untouched tail after the triple; only the prefix is binary.
private inductive A12Triple : List ℕ → Prop
  | head (L : List ℕ) : A12Triple (1::1::1::L)
  | zero {L : List ℕ} : A12Triple L → A12Triple (0::L)
  | one {L : List ℕ} : A12Triple L → A12Triple (1::L)

private theorem a12GeneralBarrier_aux (n : ℕ) :
    ∀ (L : List ℕ), L.length ≤ n → A12Triple L →
    ∀ (X : List ℕ), A12Good X → ∀ (W : List (ℕ × ℕ)),
    ∃ q, ReachesPlus target (tok_CR (X++[0,0]) W L) q ∧
      (step target q).isNone := by
  induction n with
  | zero =>
    intro L hlen hL
    cases hL <;> simp at hlen
  | succ n ih =>
    intro L hlen hL X hx W
    cases hL with
    | head L => exact a12Good_triple X hx W L
    | @zero L hL =>
      obtain ⟨X',hX',h⟩ := a12Good_zero X hx W L
      have hlen' : L.length ≤ n := by simp only [List.length_cons] at hlen; omega
      obtain ⟨q,hq,hh⟩ := ih L hlen' hL X' hX' W
      exact ⟨q,ReachesPlus.trans h hq,hh⟩
    | @one L hL =>
      cases hL with
      | head L => exact a12Good_triple X hx W (1::L)
      | @zero L hL =>
        obtain ⟨X',hX',h⟩ := a12Good_oneZero X hx W L
        have hlen' : L.length ≤ n := by simp only [List.length_cons] at hlen; omega
        obtain ⟨q,hq,hh⟩ := ih L hlen' hL X' hX' W
        exact ⟨q,ReachesPlus.trans h hq,hh⟩
      | @one L hL =>
        cases hL with
        | head L => exact a12Good_triple X hx W (1::1::L)
        | @zero L hL =>
          rcases a12Good_double X hx W 0 L with hh | ⟨X',hX',h⟩
          · exact hh
          · have hlen' : (1::L).length ≤ n := by
              simp only [List.length_cons] at hlen ⊢
              omega
            obtain ⟨q,hq,hh⟩ := ih (1::L) hlen' (.one hL) X' hX' W
            exact ⟨q,ReachesPlus.trans h hq,hh⟩
        | @one L hL => exact a12Good_triple X hx W L

private theorem a12Triple_prepend_bits (v : List Bool) (L : List ℕ)
    (hL : A12Triple L) : A12Triple (a12WordNat v ++ L) := by
  induction v with
  | nil => exact hL
  | cons b v ih =>
    cases b
    · exact .zero ih
    · exact .one ih

private theorem a12Token_pad (L : List ℕ) :
    tok_CR [3,0,0] [] L = tok_CR [3] [] L := by
  unfold tok_CR
  simp only [encTokens_succ, encTokens_zero, encTokens_nil, encLeft_nil,
    ListBlank.cons_zero_default]

private theorem a12G_token_collected (k : ℕ) (u : List Bool) :
    ReachesPlus target
      (cfg_CR_n_n [(0,0)] (List.replicate (k+1) (0,0) ++ a12WordPairs u))
      (tok_CR [3,0,0] [] (a12WordNat u.reverse ++ (List.replicate k 0 ++ [0,0,1]))) := by
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
  rw [he,a12Token_pad]
  exact ReachesPlus.trans h1 (ReachesPlus.trans h2 (ReachesPlus.trans h3 h4))

/-- Every binary pair word containing a triple of ones halts in the
prepared G corridor. No assertion of authentic blank-root reachability. -/
theorem a12G_binary_triple_halts (k : ℕ) (w v : List Bool) :
    ∃ q, ReachesPlus target
      (cfg_CR_n_n [(0,0)] (List.replicate (k+1) (0,0) ++
        a12WordPairs (w ++ [true,true,true] ++ v))) q ∧
      (step target q).isNone := by
  let L := a12WordNat w.reverse ++ (List.replicate k 0 ++ [0,0,1])
  let LL := a12WordNat v.reverse ++ 1::1::1::L
  have hL : A12Triple LL := a12Triple_prepend_bits v.reverse _ (.head L)
  have hX : A12Good [3] := .mk (by decide) (by decide) .nil
  obtain ⟨q,hq,hh⟩ := a12GeneralBarrier_aux LL.length LL (by omega) hL [3] hX []
  have h0 := a12G_token_collected k (w ++ [true,true,true] ++ v)
  have h0' : ReachesPlus target
      (cfg_CR_n_n [(0,0)] (List.replicate (k+1) (0,0) ++
        a12WordPairs (w ++ [true,true,true] ++ v))) (tok_CR [3,0,0] [] LL) := by
    simpa [LL,L,a12WordNat,List.reverse_append,List.map_append,List.append_assoc] using h0
  exact ⟨q,ReachesPlus.trans h0' hq,hh⟩

#print axioms a12Scan_zero_fatal
#print axioms a12Scan_high_fatal
#print axioms a12ExposeDoubleMany
#print axioms a12Good_double
#print axioms a12GeneralBarrier_aux
#print axioms a12G_binary_triple_halts
