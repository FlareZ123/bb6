import LagPartitionCert
import PackedReverse

namespace BB6.Agent43LagComplement
open BB6.Agent45.DelayedCarry
open BB6.Agent43ReverseSet (Walk BackCover Bits Listed omitted cover_no_omitted unionBits bit_union)
open BB6.Agent43LagPartition (PackedGroup Covered PackedCert targetFast targetFast_eq to_covered cert_empty_packed)

def weight (n i : Nat) : Nat := n+i+3

/-- Tighten the source carry bound by one for positive-length traces. -/
theorem trace_strict (n i B a : Nat) (h : Trace n i B a) : a≤n+i+1 := by
  induction h with
  | first => omega
  | step i B a x c h hx he ih =>
    have hx' : x=0 ∨ x=1 := by omega
    rcases hx' with h0|h1
    · simp [h0] at he; omega
    · simp [h1] at he; omega

theorem fixedWalk (n s B a h D d j C c : Nat) (htr : Trace n s B a)
    (hpre : Extend n s B a h D d) (hsuf : Extend n (s+h) D d j C c)
    (hj : h+j≤n) : Walk (weight n) (targetFast n B) (s+h) d j c := by
  induction hsuf with
  | nil => exact Walk.nil
  | step k C c x e hsuf hx hEq ih =>
    have hfull := extend_append n s B a h D d k C c hpre hsuf
    have htrace := extend_trace n s B a (h+k) C c htr hfull
    have hc := trace_strict n _ _ _ htrace
    obtain ⟨R,hR⟩ := extend_mod n s B a (h+k) C c hfull
    have hy := target_prefix n s (s+h+k) B R (by omega)
    rw [← hR] at hy
    apply Walk.step k c x e (ih (by omega)) hx
    · unfold weight; omega
    · rw [targetFast_eq]
      have hi : s+h+k=s+(h+k) := by omega
      rw [hy] at hEq
      simpa [weight,hi] using hEq

structure Part where
  ancestor : Nat
  bits : Nat
  word : Nat
  ends : Nat
  deriving Repr, DecidableEq

structure Plan where
  parent : PackedGroup
  parts : List Part
  deriving Repr, DecidableEq

def next (ps : List Plan) : List PackedGroup :=
  ps.flatMap fun p => p.parts.filterMap fun q =>
    if q.ends=0 then none else some ⟨q.word,q.ancestor,q.ends⟩

def PartValid (n s h : Nat) (g : PackedGroup) (q : Part) : Prop :=
  BackCover (weight n) (targetFast n g.word) (s+h) (n-h)
      (fun a => a=q.ancestor) (Bits q.bits) ∧
  (recover n g.word s h q.ancestor).1=q.word ∧
  (∀ a c, Walk (weight n) (targetFast n q.word) (s+n) a h c →
      Bits q.bits a → c<2*n+s+h+2 → Bits q.ends c)

theorem part_valid (n s h : Nat) (g : PackedGroup) (q : Part) (bad : List Nat)
    (hpart : BackCover (weight n) (targetFast n g.word) (s+h) (n-h)
      (Listed [q.ancestor]) (Bits q.bits))
    (hword : (recover n g.word s h q.ancestor).1=q.word)
    (hbad : BackCover (weight n) (targetFast n q.word) (s+n) h
      (Listed bad) (Bits (omitted (2*n+s+h+2) q.ends)))
    (hdisjoint : bad.all (fun c => !(q.bits.testBit c))=true) : PartValid n s h g q := by
  refine ⟨?_,hword,?_⟩
  · intro a c hw hc
    simpa [Listed] using hpart a c hw hc
  · intro a c hw ha hc
    exact cover_no_omitted hbad hdisjoint hw ha hc

def PlanValid (n s h : Nat) (p : Plan) : Prop :=
  unionBits (p.parts.map Part.bits)=p.parent.ends ∧
  ∀ q∈p.parts, PartValid n s h p.parent q

theorem first_covered_rev (n ends : Nat) (bad : List Nat)
    (hbad : BackCover (weight n) (targetFast n 1) 1 n
      (Listed bad) (Bits (omitted (2*n+3) ends)))
    (hdisjoint : bad.all (fun c => !((2^((n+2)/2)).testBit c))=true) :
    Covered n 1 [⟨1,(n+2)/2,ends⟩] := by
  intro B a C c htr he
  have hprefix := covered_first n B a C c htr he
  simp only [List.mem_singleton,Prod.mk.injEq] at hprefix
  rcases hprefix with ⟨rfl,rfl⟩
  have hw := fixedWalk n 1 1 ((n+2)/2) 0 1 ((n+2)/2) n C c htr
    (Extend.nil) (by simpa using he) (by omega)
  have hc := trace_strict n _ _ _ (extend_trace n 1 1 ((n+2)/2) n C c htr he)
  have hbit := cover_no_omitted hbad hdisjoint (by simpa using hw)
    (by simp [Bits] : Bits (2^((n+2)/2)) ((n+2)/2)) (by omega : c<2*n+3)
  exact ⟨⟨1,(n+2)/2,ends⟩,by simp,rfl,rfl,hbit⟩

theorem next_covered (n s h : Nat) (gs : List PackedGroup) (ps : List Plan)
    (hs : 1≤s) (hh : h≤n)
    (hparents : ps.map Plan.parent=gs)
    (hchecks : ∀ p∈ps, PlanValid n s h p)
    (hcover : Covered n s gs) : Covered n (s+h) (next ps) := by
  intro B a C c htr he
  obtain ⟨D,d,hD,hpre0⟩ := trace_split n (s+h) B a s htr hs (by omega)
  have hpre : Extend n s D d h B a := by simpa using hpre0
  obtain ⟨F,f,hmid,htail0⟩ := extend_split n (s+h) B a n C c (n-h) he (by omega)
  have hshort0 := extend_append n s D d h B a (n-h) F f hpre hmid
  have hshort : Extend n s D d n F f := by simpa only [show h+(n-h)=n by omega] using hshort0
  obtain ⟨g,hg,hword,hcarry,hend⟩ := hcover D d F f hD hshort
  rw [← hparents] at hg
  obtain ⟨p,hp,hpg⟩ := List.mem_map.mp hg
  obtain ⟨hu,hparts⟩ := hchecks p hp
  rw [← hpg,← hu] at hend
  obtain ⟨bits,hbits,hbit⟩ := bit_union _ f hend
  obtain ⟨q,hq,hqb⟩ := List.mem_map.mp hbits
  rw [← hqb] at hbit
  obtain ⟨hqpart,hqword,hqend⟩ := hparts q hq
  have hw := fixedWalk n s D d h B a (n-h) F f hD hpre hmid (by omega)
  rw [hpg,hword] at hqpart hqword
  have ha : a=q.ancestor := hqpart a f hw hbit
  have hr := recover_exact n s D d h B a hD hpre hh
  rw [← ha,hr] at hqword
  have hB : q.word=B := hqword.symm
  have htail : Extend n ((s+h)+(n-h)) F f h C c := by simpa only [show n-(n-h)=h by omega] using htail0
  have hw2 := fixedWalk n (s+h) B a (n-h) F f h C c htr hmid htail (by omega)
  have hi : s+h+(n-h)=s+n := by omega
  rw [hi,← hB] at hw2
  have hc := trace_strict n _ _ _ (extend_trace n (s+h) B a n C c htr he)
  have hbit2 := hqend f c hw2 hbit (by omega)
  have hnon : q.ends≠0 := by intro hz; simp [Bits,hz] at hbit2
  refine ⟨⟨q.word,q.ancestor,q.ends⟩,List.mem_flatMap.mpr ⟨p,hp,?_⟩,hB,ha.symm,hbit2⟩
  apply List.mem_filterMap.mpr
  exact ⟨q,hq,by simp [hnon]⟩

theorem cert_first_rev (n K ends : Nat) (bad : List Nat)
    (hbad : BackCover (weight n) (targetFast n 1) 1 n
      (Listed bad) (Bits (omitted (2*n+3) ends)))
    (hdisjoint : bad.all (fun c => !((2^((n+2)/2)).testBit c))=true)
    (hgood : MarginOK n K 1 0 [(1,(n+2)/2)]=true) :
    PackedCert n K 1 [⟨1,(n+2)/2,ends⟩] :=
  ⟨first_covered_rev n ends bad hbad hdisjoint,(cert_first n K hgood).margins⟩

theorem cert_next_rev (n K s h : Nat) (gs : List PackedGroup) (ps : List Plan)
    (hs : 1≤s) (hh : h≤n)
    (hparents : ps.map Plan.parent=gs) (hchecks : ∀ p∈ps, PlanValid n s h p)
    (hc : PackedCert n K s gs)
    (hgood : MarginOK n K s h (gs.map fun g => (g.word,g.carry))=true) :
    PackedCert n K (s+h) (next ps) := by
  refine ⟨next_covered n s h gs ps hs hh hparents hchecks hc.cover,?_⟩
  intro j hj hjs
  by_cases hle : j≤s
  · exact hc.margins j hj hle
  · exact margin_block n K s h j _ hs (by omega) hjs (to_covered n s gs hc.cover) hgood

#print axioms fixedWalk
#print axioms cert_first_rev
#print axioms cert_next_rev
end BB6.Agent43LagComplement
