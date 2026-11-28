/-!
Synchronizing reset barrier; append after GeneralTripleBarrier.
The aligned core requires no good-stack hypothesis.
-/

theorem a12ResetHazard (k : ℕ) (T : List ℕ) (W : List (ℕ × ℕ))
    (c : ℕ) (L : List ℕ) :
    ∃ q, ReachesPlus target (tok_CR (k::T) W (1::0::0::1::1::0::1::c::L)) q ∧
      (step target q).isNone := by
  have h1 := tok_CR_1_0 k T W (0::1::1::0::1::c::L)
  have h2 := tok_CR_zero 1 ((k+3)::T) W (1::1::0::1::c::L)
  have h3 := a12ExposeDouble 0 0 ((k+3)::T) W (1::c::L)
  have h4 := tok_CR_1_1_cons_25 1 (1::1::1::0::(k+3)::T) W c L
  have hs : A12Scan [1,1,1,1] [0,0,0,0] := .one (.one (.one (.one .nil)))
  obtain ⟨q,hq,hh⟩ := a12Scan_zero_fatal hs (k+3) T W c L
  exact ⟨q, ReachesPlus.trans h1 (ReachesPlus.trans h2
    (ReachesPlus.trans h3 (ReachesPlus.trans h4 hq))),hh⟩

private def a12ResetWord (c : ℕ) (L : List ℕ) :=
  1::0::0::1::1::0::1::c::L

private theorem a12Reset_good (X : List ℕ) (hx : A12Good X)
    (W : List (ℕ × ℕ)) (c : ℕ) (L : List ℕ) :
    ∃ q, ReachesPlus target (tok_CR (X++[0,0]) W (a12ResetWord c L)) q ∧
      (step target q).isNone := by
  cases hx with
  | @mk k T hk hn hT => exact a12ResetHazard k (T++[0,0]) W c L

private theorem a12Reset_delim (X : List ℕ) (hx : A12Good X)
    (W : List (ℕ × ℕ)) (c : ℕ) (L : List ℕ) :
    ∃ q, ReachesPlus target (tok_CR (X++[0,0]) W (0::a12ResetWord c L)) q ∧
      (step target q).isNone := by
  obtain ⟨X',hx',h⟩ := a12Good_zero X hx W (a12ResetWord c L)
  obtain ⟨q,hq,hh⟩ := a12Reset_good X' hx' W c L
  exact ⟨q,ReachesPlus.trans h hq,hh⟩

private inductive A12Reset : List ℕ → Prop
  | head (c : ℕ) (L : List ℕ) : A12Reset (0::0::a12ResetWord c L)
  | zero {L : List ℕ} : A12Reset L → A12Reset (0::L)
  | one {L : List ℕ} : A12Reset L → A12Reset (1::L)

private theorem a12Reset_aux (n : ℕ) :
    ∀ (L : List ℕ), L.length ≤ n → A12Reset L →
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
    | head c L =>
      obtain ⟨X',hx',h⟩ := a12Good_zero X hx W (0::a12ResetWord c L)
      obtain ⟨q,hq,hh⟩ := a12Reset_delim X' hx' W c L
      exact ⟨q,ReachesPlus.trans h hq,hh⟩
    | @zero L hL =>
      obtain ⟨X',hx',h⟩ := a12Good_zero X hx W L
      have hn : L.length ≤ n := by simp only [List.length_cons] at hlen; omega
      obtain ⟨q,hq,hh⟩ := ih L hn hL X' hx' W
      exact ⟨q,ReachesPlus.trans h hq,hh⟩
    | @one L hL =>
      cases hL with
      | head c L =>
        obtain ⟨X',hx',h⟩ := a12Good_oneZero X hx W (0::a12ResetWord c L)
        obtain ⟨q,hq,hh⟩ := a12Reset_delim X' hx' W c L
        exact ⟨q,ReachesPlus.trans h hq,hh⟩
      | @zero L hL =>
        obtain ⟨X',hx',h⟩ := a12Good_oneZero X hx W L
        have hn : L.length ≤ n := by simp only [List.length_cons] at hlen; omega
        obtain ⟨q,hq,hh⟩ := ih L hn hL X' hx' W
        exact ⟨q,ReachesPlus.trans h hq,hh⟩
      | @one L hL =>
        cases hL with
        | head c L =>
          rcases a12Good_double X hx W 0 (0::a12ResetWord c L) with hh | ⟨X',hx',h⟩
          · exact hh
          · obtain ⟨X'',hx'',h'⟩ := a12Good_oneZero X' hx' W (a12ResetWord c L)
            obtain ⟨q,hq,hh⟩ := a12Reset_good X'' hx'' W c L
            exact ⟨q,ReachesPlus.trans h (ReachesPlus.trans h' hq),hh⟩
        | @zero L hL =>
          rcases a12Good_double X hx W 0 L with hh | ⟨X',hx',h⟩
          · exact hh
          · have hn : (1::L).length ≤ n := by
              simp only [List.length_cons] at hlen ⊢
              omega
            obtain ⟨q,hq,hh⟩ := ih (1::L) hn (.one hL) X' hx' W
            exact ⟨q,ReachesPlus.trans h hq,hh⟩
        | @one L hL => exact a12Good_triple X hx W L

private theorem a12Reset_prepend (v : List Bool) (L : List ℕ)
    (hL : A12Reset L) : A12Reset (a12WordNat v ++ L) := by
  induction v with
  | nil => exact hL
  | cons b v ih =>
    cases b
    · exact .zero ih
    · exact .one ih

/-- Ordinary G binary words containing 101100100 halt. -/
theorem a12G_binary_reset_halts (k : ℕ) (w v : List Bool) :
    ∃ q, ReachesPlus target
      (cfg_CR_n_n [(0,0)] (List.replicate (k+1) (0,0) ++
        a12WordPairs (w ++ [true,false,true,true,false,false,true,false,false] ++ v))) q ∧
      (step target q).isNone := by
  let L := a12WordNat w.reverse ++ (List.replicate k 0 ++ [0,0,1])
  have hn : L ≠ [] := by simp [L]
  obtain ⟨c,T,hT⟩ := List.exists_cons_of_ne_nil hn
  let LL := a12WordNat v.reverse ++ 0::0::a12ResetWord c T
  have hL : A12Reset LL := a12Reset_prepend v.reverse _ (.head c T)
  have hX : A12Good [3] := .mk (by decide) (by decide) .nil
  obtain ⟨q,hq,hh⟩ := a12Reset_aux LL.length LL (by omega) hL [3] hX []
  have h0 := a12G_token_collected k (w ++ [true,false,true,true,false,false,true,false,false] ++ v)
  have h0' : ReachesPlus target
      (cfg_CR_n_n [(0,0)] (List.replicate (k+1) (0,0) ++
        a12WordPairs (w ++ [true,false,true,true,false,false,true,false,false] ++ v)))
      (tok_CR [3,0,0] [] LL) := by
    simpa [LL,a12ResetWord,← hT,L,a12WordNat,List.reverse_append,List.map_append,List.append_assoc] using h0
  exact ⟨q,ReachesPlus.trans h0' hq,hh⟩

#print axioms a12ResetHazard
#print axioms a12G_binary_reset_halts
