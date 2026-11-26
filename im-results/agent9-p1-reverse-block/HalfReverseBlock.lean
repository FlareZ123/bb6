import ReverseLagBlocks
import TraceComplementCover

namespace BB6.Agent9P1HalfReverseBlock

open BB6.Agent45.DelayedCarry
open BB6.Agent45ReverseBlock
open BB6.Agent43P1Complement

private theorem pow_mod_four_local (s : Nat) (hs : 2≤s) : 2^s%4=0 := by
  have hd := Nat.pow_dvd_pow 2 hs
  exact Nat.dvd_iff_mod_eq_zero.mp hd

/-- The canonical half of a delayed prefix cover, together with the
    source-derived late-margin inequalities. -/
def HalfCert (n K s : Nat) (ps : List Prefix) : Prop :=
  HalfCovered n s ps ∧
    (∀ j, 2≤j → j≤s → LateMargin n K j)

/-- Margin test on the full cover obtained by adjoining reflected
    representatives to the canonical half. -/
def halfMarginOK (n K s h : Nat) (ps : List Prefix) : Bool :=
  MarginOK n K s h (ps ++ ps.map (reflectPrefix n s))

private theorem trace_not_zero {n B a : Nat} (h : Trace n 0 B a) : False := by
  cases h

private theorem trace_one_state {n B a : Nat} (h : Trace n 1 B a) :
    B=1 ∧ a=(n+2)/2 := by
  cases h with
  | first => exact ⟨rfl,rfl⟩
  | step i B0 a0 x c0 hprev hx he =>
      exact False.elim (trace_not_zero hprev)

/-- A fitted reverse-block filter preserves the canonical half-cover.
    Unlike the generic half_next theorem, this version explicitly composes
    the source trace with blockLookahead_sound, so it applies directly to
    nextBlockByFold. -/
theorem half_covered_next_block (n s h : Nat) (ps : List Prefix)
    (parts : Nat → List (List Nat)) (hs : 2≤s)
    (hcover : HalfCovered n s ps)
    (hflat : ∀ B, (parts B).flatten = targetWord n (s+h) B n)
    (hfit : ∀ B, Fitted (n+(s+h)+3) (parts B)) :
    HalfCovered n (s+h) (nextBlockByFold n s h parts ps) := by
  intro B a C c htr hBmod hE
  obtain ⟨D,d,hpre,hExt⟩ :=
    trace_split n (s+h) B a s htr (by omega) (by omega)
  have hExt' : Extend n s D d h B a := by simpa using hExt
  obtain ⟨R,hR⟩ := extend_mod n s D d h B a hExt'
  have hDmod : D%4=1 := by
    rw [hR,Nat.add_mod,Nat.mul_mod,pow_mod_four_local s hs] at hBmod
    simpa using hBmod
  have hfull : Extend n s D d (h+n) C c :=
    extend_append n s D d h B a n C c hExt' hE
  obtain ⟨F,f,hshort⟩ :=
    extend_prefix n s D d (h+n) C c n hfull (by omega)
  have hmem := hcover D d F f hpre hDmod hshort
  have hadv := extend_in_advance n s D d h B a ps hmem hExt'
  have htrB : Trace n (s+h) B a :=
    extend_trace n s D d h B a hpre hExt'
  have hfilter : blockLookahead n (s+h) B a (parts B)=true :=
    blockLookahead_sound n (s+h) B a (parts B)
      (hflat B) (hfit B) htrB hE
  simp [nextBlockByFold,hadv,hfilter]

/-- The margin certificate composes with canonical-half reverse-block
    filtering. Margins are propagated using the reflected full cover,
    while the stored prefix list remains half-sized. -/
theorem half_cert_next_block (n K s h : Nat) (ps : List Prefix)
    (parts : Nat → List (List Nat))
    (hn : 1≤n) (heven : n%2=0) (hs : 2≤s)
    (hcert : HalfCert n K s ps)
    (hgood : halfMarginOK n K s h ps=true)
    (hflat : ∀ B, (parts B).flatten = targetWord n (s+h) B n)
    (hfit : ∀ B, Fitted (n+(s+h)+3) (parts B)) :
    HalfCert n K (s+h) (nextBlockByFold n s h parts ps) := by
  rcases hcert with ⟨hcover,hmargins⟩
  refine ⟨half_covered_next_block n s h ps parts hs hcover hflat hfit,?_⟩
  intro j hj hjs
  by_cases hle : j≤s
  · exact hmargins j hj hle
  · have hfull : Covered n s (ps ++ ps.map (reflectPrefix n s)) :=
      complete_half n s ps hn heven hs hcover
    change MarginOK n K s h (ps ++ ps.map (reflectPrefix n s))=true at hgood
    exact margin_block n K s h j (ps ++ ps.map (reflectPrefix n s))
      (by omega) (by omega) hjs hfull hgood

/-- Once the canonical half is empty, the original source has no trace at
    or beyond the corresponding delayed horizon. -/
theorem no_trace_of_half_cert_empty (n K s : Nat)
    (hn : 1≤n) (heven : n%2=0) (hs : 2≤s)
    (hcert : HalfCert n K s []) :
    ∀ m B a, n+s≤m → ¬ Trace n m B a :=
  no_trace_of_half_empty n s hn heven hs hcert.1

/-- At cost two, when n is 2 modulo 4, the unique canonical first-return
    prefix is (1,(n+2)/4). -/
theorem half_first_two (n : Nat) (hn : n%4=2) :
    HalfCovered n 2 [(1,(n+2)/4)] := by
  intro B a C c htr hBmod hE
  cases htr with
  | step _ B0 a0 x c0 hprev hx he =>
    have hbase := trace_one_state hprev
    have hx0 : x=0 := by
      have hB : (1+2*x)%4=1 := by
        simpa [hbase.1,Nat.pow_succ] using hBmod
      omega
    have hn2 : 1<n := by omega
    have ht : target n 1 1=0 := by simp [target,hn2]
    have he' := he
    simp [hbase.1,hbase.2,hx0,target,hn2] at he'
    have hc2 : 2*a=(n+2)/2 := by simpa using he'
    have hmod2 : (n+2)%2=0 := by omega
    have hdiv2 : (n+2)%2 + 2*((n+2)/2)=n+2 :=
      Nat.mod_add_div (n+2) 2
    have hc4 : 4*a=n+2 := by omega
    have hmod4 : (n+2)%4=0 := by omega
    have hdiv4 : (n+2)%4 + 4*((n+2)/4)=n+2 :=
      Nat.mod_add_div (n+2) 4
    have hc : a=(n+2)/4 := by omega
    subst x
    subst a
    simp [hbase.1,Nat.pow_succ]

/-- Initial half certificate at cost two. The single MarginOK check is
    performed on the reflected full cover, but only the canonical prefix
    needs to be stored. -/
theorem half_cert_first_two (n K : Nat) (hn : n%4=2)
    (hgood : halfMarginOK n K 2 0 [(1,(n+2)/4)]=true) :
    HalfCert n K 2 [(1,(n+2)/4)] := by
  refine ⟨half_first_two n hn,?_⟩
  intro j hj hjs
  have hj2 : j=2 := by omega
  subst j
  have hfull : Covered n 2
      ([(1,(n+2)/4)] ++ [(1,(n+2)/4)].map (reflectPrefix n 2)) :=
    complete_half n 2 [(1,(n+2)/4)] (by omega) (by omega) (by omega)
      (half_first_two n hn)
  change MarginOK n K 2 0
      ([(1,(n+2)/4)] ++ [(1,(n+2)/4)].map (reflectPrefix n 2))=true at hgood
  exact margin_block n K 2 0 2
    ([(1,(n+2)/4)] ++ [(1,(n+2)/4)].map (reflectPrefix n 2))
    (by omega) (by omega) (by omega) hfull hgood

/-- The reflected full-prefix margin test at the actual n=45,352,466
    cost-two seed is true for K=250,000,000. The proof only needs 2^64
    as a lower bound; it does not normalize the enormous power 2^n. -/
theorem half_margin_ok_n45352466 :
    halfMarginOK 45352466 250000000 2 0
      [(1,(45352466+2)/4)] = true := by
  have hpow : 2^64 ≤ 2^45352466 :=
    Nat.pow_le_pow_right (by decide : 0<2) (by norm_num)
  have hnum :
      (45352466+250000000+2)*marginSize 45352466 250000000*4
        < 6*2^64 := by
    norm_num [marginSize]
  have hineq :
      (45352466+250000000+2)*marginSize 45352466 250000000*4
        < 6*2^45352466 := by
    exact lt_of_lt_of_le hnum (Nat.mul_le_mul_left 6 hpow)
  simp [halfMarginOK,MarginOK,marginSize,reflectPrefix,cap,resMin,hineq]

/-- The actual n=45,352,466 seed has a fully source-checked canonical
    half certificate at cost two for K=250,000,000. -/
theorem half_cert_n45352466 :
    HalfCert 45352466 250000000 2 [(1,(45352466+2)/4)] :=
  half_cert_first_two 45352466 250000000 (by norm_num) half_margin_ok_n45352466

#print axioms half_covered_next_block
#print axioms half_cert_next_block
#print axioms no_trace_of_half_cert_empty
#print axioms half_first_two
#print axioms half_cert_first_two
#print axioms half_margin_ok_n45352466
#print axioms half_cert_n45352466

end BB6.Agent9P1HalfReverseBlock
