import ReverseBlockLagTrace
import LagCert

namespace BB6.Agent45ReverseBlock

open BB6.Agent45.DelayedCarry

/-- Any authentic n-step delayed extension is a chronological fixed-target
    Walk. The changing low word does not change its first n delayed bits. -/
theorem extend_to_walk (n s B a k C c : Nat)
    (hTrace : Trace n s B a) (hk : k≤n)
    (hExt : Extend n s B a k C c) :
    Walk (n+s+3+k) c (targetWord n s B k) a := by
  induction hExt with
  | nil =>
    have ha := (trace_bounds n s B a hTrace).2.2.2
    exact Walk.nil (by omega)
  | @step k C c x d h hx he ih =>
    obtain ⟨R,hR⟩ := extend_mod n s B a k C c h
    have htarget := target_prefix n s (s+k) B R (by omega)
    have hprev := extend_trace n s B a k C c hTrace h
    have hc : c<n+s+k+3 := by
      have hb := (trace_bounds n (s+k) C c hprev).2.2.2
      omega
    have hyC := target_bound n (s+k) C
    have hd : d<n+s+k+3 := by
      rcases (show x=0 ∨ x=1 by omega) with h0|h1
      · subst x
        simp at he
        omega
      · subst x
        simp at he
        omega
    have heB : 2*d+target n (s+k) B =
        c+x*(n+s+k+3) := by
      rw [hR] at he
      rw [htarget] at he
      simpa [Nat.add_assoc] using he
    have hsingle :
        Walk (n+s+3+(k+1)) d [target n (s+k) B] c := by
      refine Walk.step [] d (target n (s+k) B) x c
        (Walk.nil (by omega)) (target_bound n (s+k) B) hx
        (by omega) (by omega) ?_
      omega
    have hcomp := walk_append hsingle ih
    simpa [targetWord,Nat.add_assoc] using hcomp

/-- Exact Boolean lookahead computed by a fitted reverse-block partition. -/
def blockLookahead (n s B a : Nat) (bs : List (List Nat)) : Bool :=
  decide (a ∈ blockFold (n+s+3) bs
    (List.range (n+s+3+bs.flatten.length)))

/-- A genuine extension always survives the fitted reverse-block lookahead.
    This is the sound direction needed for certified pruning: false positives
    are harmless, while an empty image proves that no extension exists. -/
theorem blockLookahead_sound (n s B a : Nat) (bs : List (List Nat))
    (hflat : bs.flatten=targetWord n s B n)
    (hfit : Fitted (n+s+3) bs)
    (hTrace : Trace n s B a) {C c : Nat}
    (hExt : Extend n s B a n C c) :
    blockLookahead n s B a bs = true := by
  have hbits : ∀ y∈bs.flatten, y≤1 := by
    rw [hflat]
    exact targetWord_bits n s B n
  have hwalk := extend_to_walk n s B a n C c hTrace (by omega) hExt
  have hwalk' : Walk (n+s+3+bs.flatten.length) c bs.flatten a := by
    simpa [hflat,targetWord_length] using hwalk
  have htr := extend_trace n s B a n C c hTrace hExt
  have hb := (trace_bounds n (s+n) C c htr).2.2.2
  have hc : c<n+s+3+bs.flatten.length := by
    rw [hflat]
    simp [targetWord_length]
    omega
  have hmem := (mem_blockFold (n+s+3) a bs
    (List.range (n+s+3+bs.flatten.length)) hbits hfit).2
    ⟨c,List.mem_range.mpr hc,hwalk'⟩
  unfold blockLookahead
  exact decide_eq_true_eq.mpr hmem

/-- The next-prefix filter using fitted reverse blocks instead of a
    bit-by-bit forward lookahead. The partition may be chosen per low word. -/
def nextBlockByFold (n s h : Nat)
    (parts : Nat → List (List Nat)) (ps : List Prefix) : List Prefix :=
  (advance n s ps h).filter fun p =>
    blockLookahead n (s+h) p.1 p.2 (parts p.1)

/-- A fitted-block reverse filter preserves every authentic prefix with an
    n-step continuation. This is the exact Covered integration. -/
theorem covered_next_block (n s h : Nat) (ps : List Prefix)
    (parts : Nat → List (List Nat))
    (hs : 1≤s) (hcover : Covered n s ps)
    (hflat : ∀ B, (parts B).flatten =
      targetWord n (s+h) B n)
    (hfit : ∀ B, Fitted (n+(s+h)+3) (parts B)) :
    Covered n (s+h) (nextBlockByFold n s h parts ps) := by
  intro B a C c htr hE
  obtain ⟨D,d,hpre,hExt⟩ :=
    trace_split n (s+h) B a s htr hs (by omega)
  have hExt' : Extend n s D d h B a := by simpa using hExt
  have hfull : Extend n s D d (h+n) C c :=
    extend_append n s D d h B a n C c hExt' hE
  obtain ⟨F,f,hshort⟩ :=
    extend_prefix n s D d (h+n) C c n hfull (by omega)
  have hm := hcover D d F f hpre hshort
  have hm' := extend_in_advance n s D d h B a ps hm hExt'
  have hfilter : blockLookahead n (s+h) B a (parts B)=true :=
    blockLookahead_sound n (s+h) B a (parts B)
      (hflat B) (hfit B) htr hE
  simp [nextBlockByFold,hm',hfilter]

/-- The full delayed margin certificate composes unchanged with fitted
    reverse-block lookahead. -/
theorem cert_next_block (n K s h : Nat) (ps : List Prefix)
    (parts : Nat → List (List Nat))
    (hs : 1≤s) (hcert : Cert n K s ps)
    (hgood : MarginOK n K s h ps=true)
    (hflat : ∀ B, (parts B).flatten =
      targetWord n (s+h) B n)
    (hfit : ∀ B, Fitted (n+(s+h)+3) (parts B)) :
    Cert n K (s+h) (nextBlockByFold n s h parts ps) := by
  refine ⟨covered_next_block n s h ps parts hs hcert.cover hflat hfit,?_⟩
  intro j hj hjs
  by_cases hle : j≤s
  · exact hcert.margins j hj hle
  · exact margin_block n K s h j ps hs (by omega) hjs hcert.cover hgood

#print axioms extend_to_walk
#print axioms blockLookahead_sound
#print axioms covered_next_block
#print axioms cert_next_block

end BB6.Agent45ReverseBlock
