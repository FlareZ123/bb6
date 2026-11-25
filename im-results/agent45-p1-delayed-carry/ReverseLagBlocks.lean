import ReverseBlockCompose
import ReverseLagCore

namespace BB6.Agent45ReverseBlock

open BB6.Agent45.DelayedCarry
open BB6.Agent23ReverseLag

/-- One fixed delayed bit is exactly one reverse-block step. -/
theorem edgeY_to_walk {q y c z : Nat} (h : EdgeY q y c z) :
    Walk (q+1) z [y] c := by
  rcases h with ⟨hc,hz,hy,hbranch⟩
  rcases hbranch with h0|h1
  · exact Walk.step [] z y 0 c (Walk.nil (by omega)) hy (by omega)
      (by omega) (by omega) (by simpa using h0)
  · exact Walk.step [] z y 1 c (Walk.nil (by omega)) hy (by omega)
      (by omega) (by omega) (by simpa using h1)

/-- Conversely, a legal one-bit Walk edge has the exact modular predecessor
    equation and both strict carry bounds. -/
theorem walk_to_edgeY {q y c z : Nat} (h : Walk (q+1) z [y] c)
    (hy : y≤1) : EdgeY q y c z := by
  obtain ⟨B,hB,he⟩ := eq_of_walk h
  have hBlt : B<2 := by simpa using hB
  have hBmod : B%2=B := Nat.mod_eq_of_lt hBlt
  have he' : 2*z+y+B=(q+1)*B+c := by
    simpa [digits,corr,hBmod] using he
  have hEq : 2*z+y=c+q*B := by omega
  have hB01 : B=0 ∨ B=1 := by omega
  have hc : c<q := by
    have hh := walk_bound h
    simpa using hh
  have hz : z<q := by
    rcases hB01 with h0|h1 <;> subst B <;> omega
  refine ⟨hc,hz,hy,?_⟩
  rcases hB01 with h0|h1
  · exact Or.inl (by simpa [h0] using hEq)
  · exact Or.inr (by simpa [h1] using hEq)

/-- The delayed reverse path and the exact fixed-bit Walk are equivalent.
    DWalk stores the newest bit at the head; Walk consumes the chronological
    word, hence the reversal. -/
theorem dWalk_iff_walk {q c : Nat} {ys : List Nat} {z : Nat}
    (hys : ∀ y∈ys, y≤1) :
    DWalk q c ys z ↔ Walk (q+ys.length) z ys.reverse c := by
  constructor
  · intro h
    induction h with
    | nil q c => exact Walk.nil (by omega)
    | @snoc q c ys d y w hprev hedge ih =>
      have hsingle : Walk (q+ys.length+1) w [y] d := by
        simpa [Nat.add_assoc] using edgeY_to_walk hedge
      have htail : Walk (q+ys.length) d ys.reverse c := ih
      simpa [List.reverse_cons,Nat.add_assoc] using
        walk_append hsingle htail
  · intro h
    induction ys generalizing c z with
    | nil =>
      simp only [List.reverse_nil,List.length_nil,Nat.add_zero] at h
      cases h
      exact DWalk.nil q c
    | cons y ys ih =>
      have hy : y≤1 := hys y (by simp)
      have hys' : ∀ b∈ys, b≤1 := by
        intro b hb
        exact hys b (List.mem_cons_of_mem y hb)
      have hform : Walk (q+ys.length+1) z (ys.reverse++[y]) c := by
        simpa [List.reverse_cons,Nat.add_assoc] using h
      obtain ⟨d,hsingle,htail⟩ :=
        walk_split (q+ys.length+1) z ys.reverse [y] c hform
      have htail' : Walk (q+ys.length) d ys.reverse c := by
        simpa using htail
      have hprev : DWalk q c ys d := ih hys' htail'
      have hedge : EdgeY (q+ys.length) y d z :=
        walk_to_edgeY hsingle hy
      exact DWalk.snoc q c ys d y z hprev hedge

/-- Exact Boolean lookahead using a fitted reverse-block partition of the
    delayed target. The terminal interval is the full carry range at the
    end of the n-bit extension. -/
def blockLookahead (n s B a : Nat) (bs : List (List Nat)) : Bool :=
  decide (a ∈ blockFold (n+s+3) bs
    (List.range (n+s+3+bs.flatten.length)))

theorem blockLookahead_iff_extend (n s B a : Nat) (bs : List (List Nat))
    (hn : 0<n) (hTrace : Trace n s B a)
    (hflat : bs.flatten = (targetsRev n s B n).reverse)
    (hfit : Fitted (n+s+3) bs) :
    blockLookahead n s B a bs = true ↔
      ∃ C c, Extend n s B a n C c := by
  have hlen : bs.flatten.length=n := by
    rw [hflat]
    simp
  have hbits : ∀ y∈bs.flatten, y≤1 := by
    intro y hy
    have hy' : y∈targetsRev n s B n := by
      rw [hflat] at hy
      simpa using hy
    exact targetsRev_bits n s B n y hy'
  have hbitsRev : ∀ y∈targetsRev n s B n, y≤1 :=
    targetsRev_bits n s B n
  have hmem := mem_blockFold (n+s+3) a bs
    (List.range (n+s+3+bs.flatten.length)) hbits hfit
  rw [blockLookahead,decide_eq_true_eq,hmem]
  constructor
  · rintro ⟨z,hz,hwalk⟩
    have hwalk' :
        Walk (n+s+3+(targetsRev n s B n).length) z
          (targetsRev n s B n).reverse a := by
      simpa [hflat,targetsRev_length] using hwalk
    have hD : DWalk (n+s+3) a (targetsRev n s B n) z :=
      (dWalk_iff_walk hbitsRev).2 hwalk'
    obtain ⟨C,hExt⟩ := dWalk_to_extend n s B a n z (by omega) hD
    exact ⟨C,z,hExt⟩
  · rintro ⟨C,c,hExt⟩
    have hD := extend_to_DWalk n s B a n C c hn hTrace hExt
    have hwalk := (dWalk_iff_walk hbitsRev).1 hD
    have hwalk' : Walk (n+s+3+bs.flatten.length) c bs.flatten a := by
      simpa [hflat,targetsRev_length] using hwalk
    have htr := extend_trace n s B a n C c hTrace hExt
    have hb := (trace_bounds n (s+n) C c htr).2.2.2
    have hc : c<n+s+3+bs.flatten.length := by
      rw [hlen]
      omega
    exact ⟨c,List.mem_range.mpr hc,hwalk'⟩

/-- The next-prefix filter using fitted reverse blocks instead of a
    bit-by-bit reverse-live pass. The partition may be chosen per low word. -/
def nextBlockByFold (n s h : Nat)
    (parts : Nat → List (List Nat)) (ps : List Prefix) : List Prefix :=
  (advance n s ps h).filter fun p =>
    blockLookahead n (s+h) p.1 p.2 (parts p.1)

/-- A fitted-block reverse filter preserves every authentic prefix with an
    n-step continuation. This is the exact Covered integration. -/
theorem covered_next_block (n s h : Nat) (ps : List Prefix)
    (parts : Nat → List (List Nat))
    (hn : 0<n) (hS : 1≤s) (hcover : Covered n s ps)
    (hflat : ∀ B, (parts B).flatten =
      (targetsRev n (s+h) B n).reverse)
    (hfit : ∀ B, Fitted (n+(s+h)+3) (parts B)) :
    Covered n (s+h) (nextBlockByFold n s h parts ps) := by
  intro B a C c htr hE
  obtain ⟨D,d,hpre,hExt⟩ :=
    trace_split n (s+h) B a s htr hS (by omega)
  have hExt' : Extend n s D d h B a := by simpa using hExt
  have hfull : Extend n s D d (h+n) C c :=
    extend_append n s D d h B a n C c hExt' hE
  obtain ⟨F,f,hshort⟩ :=
    extend_prefix n s D d (h+n) C c n hfull (by omega)
  have hm := hcover D d F f hpre hshort
  have hm' := extend_in_advance n s D d h B a ps hm hExt'
  have hfilter : blockLookahead n (s+h) B a (parts B)=true :=
    (blockLookahead_iff_extend n (s+h) B a (parts B)
      hn htr (hflat B) (hfit B)).2 ⟨C,c,hE⟩
  simp [nextBlockByFold,hm',hfilter]

#print axioms edgeY_to_walk
#print axioms walk_to_edgeY
#print axioms dWalk_iff_walk
#print axioms blockLookahead_iff_extend
#print axioms covered_next_block

end BB6.Agent45ReverseBlock
