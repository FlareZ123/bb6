/-!
Nonbinary triple barrier. Append after GeneralTripleBarrier, whose
A12Pairable grammar includes the protected zero cut. See NonbinaryTripleBarrier.md.
-/

private theorem a12G_to_EL_tokens (k : ℕ) (U : List (ℕ × ℕ)) :
    ReachesPlus target
      (cfg_CR_n_n [(0,0)] (List.replicate (k+1) (0,0) ++ U))
      (tok_EL (U.map (fun p => p.1+1) ++ [0,0]) []
        (0::List.replicate k 0 ++ [0,0,1])) := by
  let K := U.map (fun p => p.1+1) ++ [0,0]
  have he : cfg_CR_n_n [(0,0)] (List.replicate (k+1) (0,0) ++ U) =
      tok_CR (List.replicate (k+1) 1 ++ K) [] [0] := by
    unfold cfg_CR_n_n tok_CR
    rw [encRight_eq_nat, ← a12Tokens_pairs (List.replicate (k+1) (0,0) ++ U)]
    simp [K,List.map_append,List.map_replicate,List.append_assoc]
  have h1 := tok_CR_zero 1 (List.replicate k 1 ++ K) [] []
  have h2 := tok_CR_add2_nil_21 1 (List.replicate k 1 ++ K) []
  have h3 := a12_el_sweep k K [] [0,0,1]
  rw [he]
  exact ReachesPlus.trans h1 (ReachesPlus.trans h2 h3)

private theorem a12Scan_binary_continue (w : List Bool)
    (K : List ℕ) (W : List (ℕ × ℕ)) (L : List ℕ)
    (hh : ∃ q, ReachesPlus target (tok_EL K W (0::a12WordNat w.reverse++L)) q ∧
      (step target q).isNone) :
    ∃ q, ReachesPlus target (tok_EL (a12WordTokens w++K) W (0::L)) q ∧
      (step target q).isNone := by
  induction w generalizing L with
  | nil => exact hh
  | cons b w ih =>
    cases b
    · obtain ⟨q,hq,hhalt⟩ := ih (0::L) (by
        simpa [a12WordNat,List.reverse_cons,List.map_append,List.append_assoc] using hh)
      have h1 := tok_EL_1 (a12WordTokens w++K) W (0::L)
      exact ⟨q,ReachesPlus.trans h1 hq,hhalt⟩
    · obtain ⟨q,hq,hhalt⟩ := ih (1::L) (by
        simpa [a12WordNat,List.reverse_cons,List.map_append,List.append_assoc] using hh)
      have h1 := tok_EL_2 (a12WordTokens w++K) W L
      exact ⟨q,ReachesPlus.trans h1 hq,hhalt⟩

private theorem a12EntryExtraOne (z a : ℕ) (T : List ℕ) (W : List (ℕ × ℕ))
    (L : List ℕ) :
    ReachesPlus target
      (tok_EL (2::List.replicate z 1++(a+3)::T) W (0::L))
      (tok_DR (2::a::T) W (List.replicate (z+1) 0++1::L)) := by
  cases z with
  | zero =>
    exact ReachesPlus.trans (tok_EL_2 ((a+3)::T) W L)
      (tok_EL_add3 a T W (0::1::L))
  | succ z =>
    have h1 := tok_EL_2 (List.replicate (z+1) 1++(a+3)::T) W L
    have h2 := a12_el_sweep z ((a+3)::T) W (0::1::L)
    rw [a12_rep_push 0 (z+1) (1::L)] at h2
    have h3 := tok_EL_add3 a T W (List.replicate (z+2) 0++1::L)
    exact ReachesPlus.trans h1 (ReachesPlus.trans h2 h3)

private theorem a12EntryExtraOneReturn (z a : ℕ) (T : List ℕ) (W : List (ℕ × ℕ))
    (L : List ℕ) :
    ReachesPlus target
      (tok_EL (2::List.replicate z 1++(a+3)::T) W (0::L))
      (tok_CR (List.replicate (z+3) 1++a::T) W (0::L)) := by
  have h1 := a12EntryExtraOne z a T W L
  have h2 := a12_dr_sweep z (a::T) W (1::L)
  have h3 := tok_DR_succ (List.replicate (z+1) 1++a::T) W 0 L
  exact ReachesPlus.trans h1 (ReachesPlus.trans h2 h3)

private theorem a12Good_entry_zero (z : ℕ) (T : List ℕ) :
    A12Good (List.replicate (z+3) 1++0::T) := by
  exact .mk (by decide) (by decide) (a12Pairable_ones (z+2) _ (.cut T))

private theorem a12Good_entry_paired (z a : ℕ) (T : List ℕ) (hT : A12Pairable T) :
    A12Good (List.replicate (z+3) 1++a::T) := by
  have hPair : A12Pairable (1::a::T) := by
    by_cases ha : a=2
    · subst a
      exact .pair hT
    · exact .other (by decide) (.other ha hT)
  have hTail := a12Pairable_ones (z+1) (1::a::T) hPair
  rw [a12_rep_push 1 (z+1) (a::T)] at hTail
  exact .mk (by decide) (by decide) hTail

private theorem a12G_nonbinary_triple_core (k z a : ℕ)
    (w v : List Bool) (T : List (ℕ × ℕ))
    (hx : A12Good (List.replicate (z+3) 1++a::T.map (fun p => p.1+1))) :
    ∃ q, ReachesPlus target
      (cfg_CR_n_n [(0,0)] (List.replicate (k+1) (0,0) ++
        a12WordPairs (w++[true,true,true]++v++[true]) ++
        List.replicate z (0,0) ++ (a+2,0)::T)) q ∧ (step target q).isNone := by
  let u := w++[true,true,true]++v
  let R := T.map (fun p => p.1+1)
  let E := 2::List.replicate z 1++(a+3)::R++[0,0]
  let L := List.replicate k 0 ++ [0,0,1]
  let LL := a12WordNat u.reverse ++ L
  have ht : A12Triple LL := by
    have h := a12Triple_prepend_bits v.reverse (1::1::1::(a12WordNat w.reverse++L))
      (.head (a12WordNat w.reverse++L))
    simpa [LL,u,a12WordNat,List.reverse_append,List.map_append,List.append_assoc] using h
  have h1 := a12G_to_EL_tokens k
    (a12WordPairs (u++[true])++List.replicate z (0,0)++(a+2,0)::T)
  have h1' : ReachesPlus target
      (cfg_CR_n_n [(0,0)] (List.replicate (k+1) (0,0) ++
        a12WordPairs (u++[true])++List.replicate z (0,0)++(a+2,0)::T))
      (tok_EL (a12WordTokens u++E) [] (0::L)) := by
    simpa [E,R,L,a12WordTokens,a12WordPairs,List.map_append,List.map_replicate,
      List.append_assoc] using h1
  have h2 := a12EntryExtraOneReturn z a (R++[0,0]) [] LL
  obtain ⟨q,hq,hh⟩ := a12GeneralBarrier_aux (0::LL).length (0::LL) (by omega)
    (.zero ht) (List.replicate (z+3) 1++a::R) hx []
  have h2' : ReachesPlus target (tok_EL E [] (0::LL)) q := by
    have h2'' : ReachesPlus target (tok_EL E [] (0::LL))
        (tok_CR ((List.replicate (z+3) 1++a::R)++[0,0]) [] (0::LL)) := by
      simpa [E,List.append_assoc] using h2
    exact ReachesPlus.trans h2'' hq
  obtain ⟨q',hq',hh'⟩ := a12Scan_binary_continue u E [] L ⟨q,h2',hh⟩
  exact ⟨q',ReachesPlus.trans h1' hq',hh'⟩

/-- An arbitrary nonbinary right tail is permitted after the entry 2. -/
theorem a12G_triple_before_two_halts (k z : ℕ)
    (w v : List Bool) (T : List (ℕ × ℕ)) :
    ∃ q, ReachesPlus target
      (cfg_CR_n_n [(0,0)] (List.replicate (k+1) (0,0) ++
        a12WordPairs (w++[true,true,true]++v++[true]) ++
        List.replicate z (0,0) ++ (2,0)::T)) q ∧ (step target q).isNone := by
  exact a12G_nonbinary_triple_core k z 0 w v T
    (a12Good_entry_zero z (T.map (fun p => p.1+1)))

inductive a12PairedOrdinary : List (ℕ × ℕ) → Prop
  | nil : a12PairedOrdinary []
  | other {x : ℕ × ℕ} {T} (hx : x.1 ≠ 1) :
      a12PairedOrdinary T → a12PairedOrdinary (x::T)
  | pair {b c : ℕ} {T} : a12PairedOrdinary T →
      a12PairedOrdinary ((0,b)::(1,c)::T)

private theorem a12PairedOrdinary_tokens {T : List (ℕ × ℕ)}
    (h : a12PairedOrdinary T) : A12Pairable (T.map (fun p => p.1+1)) := by
  induction h with
  | nil => exact .nil
  | @other x T hx h ih =>
    exact .other (by omega) ih
  | pair h ih => exact .pair ih

/-- Any entry >=2 with a paired ordinary tail is fatal after a protected triple. -/
theorem a12G_triple_before_high_halts (k z a : ℕ)
    (w v : List Bool) (T : List (ℕ × ℕ)) (hT : a12PairedOrdinary T) :
    ∃ q, ReachesPlus target
      (cfg_CR_n_n [(0,0)] (List.replicate (k+1) (0,0) ++
        a12WordPairs (w++[true,true,true]++v++[true]) ++
        List.replicate z (0,0) ++ (a+2,0)::T)) q ∧ (step target q).isNone := by
  exact a12G_nonbinary_triple_core k z a w v T
    (a12Good_entry_paired z a _ (a12PairedOrdinary_tokens hT))

#print axioms a12G_triple_before_two_halts
#print axioms a12G_triple_before_high_halts
