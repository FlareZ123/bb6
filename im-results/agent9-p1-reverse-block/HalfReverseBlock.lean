import ReverseLagBlocks
import TraceComplementCover

namespace BB6.Agent9P1HalfReverseBlock

open BB6.Agent45.DelayedCarry
open BB6.Agent45ReverseBlock
open BB6.Agent43P1Complement

private theorem pow_mod_four_local (s : Nat) (hs : 2≤s) : 2^s%4=0 := by
  have hd := Nat.pow_dvd_pow 2 hs
  exact Nat.dvd_iff_mod_eq_zero.mp (by simpa using hd)

/-- The canonical half of a delayed prefix cover, together with the
    source-derived late-margin inequalities. -/
def HalfCert (n K s : Nat) (ps : List Prefix) : Prop :=
  HalfCovered n s ps ∧
    (∀ j, 2≤j → j≤s → LateMargin n K j)

/-- Margin test on the full cover obtained by adjoining reflected
    representatives to the canonical half. -/
def halfMarginOK (n K s h : Nat) (ps : List Prefix) : Bool :=
  MarginOK n K s h (ps ++ ps.map (reflectPrefix n s))

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
    extend_trace n s D d h hpre hExt'
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
  | step i B0 a0 x c0 hprev hx he =>
    cases hprev with
    | first =>
      have hi : i=1 := by omega
      subst i
      have hx0 : x=0 := by
        have hB : (1+2*x)%4=1 := by simpa [Nat.pow_succ] using hBmod
        omega
      have hn2 : 1<n := by omega
      have ht : target n 1 1=0 := by simp [target,hn2]
      have hq : (n+2)/2=2*((n+2)/4) := by omega
      have hc : c0=(n+2)/4 := by
        rw [ht] at he
        rw [hx0] at he
        omega
      subst x
      subst c0
      simp [Nat.pow_succ]
    | step i' B' a' x' c' hprev' hx' he' =>
      omega

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

#print axioms half_covered_next_block
#print axioms half_cert_next_block
#print axioms no_trace_of_half_cert_empty
#print axioms half_first_two
#print axioms half_cert_first_two

end BB6.Agent9P1HalfReverseBlock
