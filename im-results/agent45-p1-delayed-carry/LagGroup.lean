import LagPartition
import LagCert
namespace BB6.Agent45.DelayedCarry

theorem fixedRun_suffix_sound (L n s B a k C c r D d bits : Nat)
    (htr : Trace n s B a) (hpre : Extend n s B a k C c)
    (he : Extend n (s+k) C c r D d) (hr : k+r≤n)
    (hb : n+s+k+r+2<2^L) (hbit : bits.testBit c=true) :
    (fixedRun L n B (s+k) bits r).testBit d=true := by
  induction he with
  | nil => exact hbit
  | step j D d x e he hx hEq ih =>
    have hprev := ih (by omega) (by omega)
    have hnon : fixedRun L n B (s+k) bits j ≠ 0 := by intro hz; rw [hz] at hprev; simp at hprev
    have hfull := extend_append n s B a k C c j D d hpre he
    obtain ⟨R,hR⟩ := extend_mod n s B a (k+j) D d hfull
    have hy := target_prefix n s (s+k+j) B R (by omega)
    rw [← hR] at hy
    have htrace := extend_trace n (s+k) C c (j+1) (D+2^(s+k+j)*x) e
      (extend_trace n s B a k C c htr hpre) (Extend.step j D d x e he hx hEq)
    have hbound := (trace_bounds n _ _ _ htrace).2.2.2
    rw [fixedRun_add]
    simp only [fixedRun,if_neg hnon]
    exact lagStep_sound L (n+(s+k+j)+3) (target n (s+k+j) B) _ d x e hx (by omega) hprev (by rw [← hy]; exact hEq)

structure Group where
  word : Nat
  carry : Nat
  ends : List Nat
  deriving Repr, DecidableEq

def GroupCovered (n s : Nat) (gs : List Group) : Prop :=
  ∀ B a C c, Trace n s B a → Extend n s B a n C c →
    ∃ g∈gs, g.word=B ∧ g.carry=a ∧ c∈g.ends

def extractBits (bound bits : Nat) : List Nat := (List.range bound).filter (fun c => bits.testBit c)

theorem extract_sound (bound bits c : Nat) (hb : c<bound) (hbit : bits.testBit c=true) :
    c∈extractBits bound bits := by simp [extractBits,hb,hbit]

def groupFirst (L n : Nat) : List Group :=
  [⟨1,(n+2)/2,extractBits (2*n+4) (lookahead L n 1 1 ((n+2)/2) n)⟩]

theorem group_first_covered (L n : Nat) (hb : 2*n+3<2^L) : GroupCovered n 1 (groupFirst L n) := by
  intro B a C c htr he
  have hprefix := covered_first n B a C c htr he
  simp only [List.mem_singleton,Prod.mk.injEq] at hprefix
  rcases hprefix with ⟨rfl,rfl⟩
  have hbound := (trace_bounds n _ _ _ (extend_trace n 1 1 ((n+2)/2) n C c htr he)).2.2.2
  refine ⟨⟨1,(n+2)/2,extractBits (2*n+4) (lookahead L n 1 1 ((n+2)/2) n)⟩,by simp [groupFirst],rfl,rfl,?_⟩
  exact extract_sound _ _ _ (by omega) (lookahead_sound L n 1 1 ((n+2)/2) n C c htr he (by omega) (by omega))

def advanceGroup (L n s h : Nat) (g : Group) : List Group :=
  (backGroups n g.word (s+h) (n-h) (leafEntries g.ends)).filterMap fun p =>
    let r := recover n g.word s h p.1
    let ends := extractBits (2*n+s+h+3) (fixedRun L n r.1 (s+n) p.2.bits h)
    if ends.isEmpty then none else some ⟨r.1,p.1,ends⟩

def groupNext (L n s h : Nat) (gs : List Group) : List Group := gs.flatMap (advanceGroup L n s h)

theorem group_next_covered (L n s h : Nat) (gs : List Group) (hs : 1≤s) (hh : h≤n)
    (hb : 2*n+s+h+2<2^L) (hcover : GroupCovered n s gs) :
    GroupCovered n (s+h) (groupNext L n s h gs) := by
  intro B a C c htr he
  obtain ⟨D,d,hD,hpre0⟩ := trace_split n (s+h) B a s htr hs (by omega)
  have hpre : Extend n s D d h B a := by simpa using hpre0
  obtain ⟨F,f,hmid,htail0⟩ := extend_split n (s+h) B a n C c (n-h) he (by omega)
  have hshort0 := extend_append n s D d h B a (n-h) F f hpre hmid
  have hshort : Extend n s D d n F f := by simpa only [show h+(n-h)=n by omega] using hshort0
  obtain ⟨g,hg,hword,hcarry,hend⟩ := hcover D d F f hD hshort
  have hrev := rewind_exact n s D d h B a (n-h) F f hD hpre hmid (by omega)
  have hbck := backGroups_cover n g.word (s+h) (n-h) f f (leafEntries g.ends) (leaf_cover g.ends f hend)
  rw [hword,hrev] at hbck
  obtain ⟨t,ht,hhas⟩ := hbck
  have hr := recover_exact n s D d h B a hD hpre hh
  have ht' : (a,t)∈backGroups n g.word (s+h) (n-h) (leafEntries g.ends) := by simpa [hword] using ht
  have htail : Extend n ((s+h)+(n-h)) F f h C c := by simpa only [show n-(n-h)=h by omega] using htail0
  have hbit := fixedRun_suffix_sound L n (s+h) B a (n-h) F f h C c t.bits htr hmid htail (by omega) (by omega) (EndTree.bit_of_has t f hhas)
  have hidx : s+h+(n-h)=s+n := by omega
  rw [hidx] at hbit
  let ends := extractBits (2*n+s+h+3) (fixedRun L n B (s+n) t.bits h)
  have hbound := (trace_bounds n _ _ _ (extend_trace n (s+h) B a n C c htr he)).2.2.2
  have hc : c∈ends := extract_sound _ _ _ (by omega) hbit
  have hnon : ends.isEmpty=false := by
    cases hE : ends with
    | nil => rw [hE] at hc; simp at hc
    | cons => rfl
  refine ⟨⟨B,a,ends⟩,List.mem_flatMap.mpr ⟨g,hg,?_⟩,rfl,rfl,hc⟩
  unfold advanceGroup
  apply List.mem_filterMap.mpr
  refine ⟨(a,t),ht',?_⟩
  simp only [hword,hr]
  change (if ends.isEmpty then (none : Option Group) else some ⟨B,a,ends⟩)=some ⟨B,a,ends⟩
  simp [hnon]

theorem covered_of_groups (n s : Nat) (gs : List Group) (h : GroupCovered n s gs) :
    Covered n s (gs.map fun g => (g.word,g.carry)) := by
  intro B a C c htr he
  obtain ⟨g,hg,hw,hc,he⟩ := h B a C c htr he
  exact List.mem_map.mpr ⟨g,hg,by simp [hw,hc]⟩

structure GroupCert (n K s : Nat) (gs : List Group) : Prop where
  cover : GroupCovered n s gs
  margins : ∀ j, 1≤j → j≤s → LateMargin n K j

theorem group_cert_first (L n K : Nat) (hb : 2*n+3<2^L)
    (hgood : MarginOK n K 1 0 [(1,(n+2)/2)]=true) : GroupCert n K 1 (groupFirst L n) :=
  ⟨group_first_covered L n hb,(cert_first n K hgood).margins⟩

theorem group_cert_next (L n K s h : Nat) (gs : List Group) (hs : 1≤s) (hh : h≤n)
    (hb : 2*n+s+h+2<2^L) (hc : GroupCert n K s gs)
    (hgood : MarginOK n K s h (gs.map fun g => (g.word,g.carry))=true) :
    GroupCert n K (s+h) (groupNext L n s h gs) := by
  refine ⟨group_next_covered L n s h gs hs hh hb hc.cover,?_⟩
  intro j hj hjs
  by_cases hle : j≤s
  · exact hc.margins j hj hle
  · exact margin_block n K s h j _ hs (by omega) hjs (covered_of_groups n s gs hc.cover) hgood

theorem group_cert_empty (n K s : Nat) (h : GroupCert n K s []) : Cert n K s [] :=
  ⟨covered_of_groups n s [] h.cover,h.margins⟩

#print axioms group_next_covered
#print axioms group_cert_next
end BB6.Agent45.DelayedCarry
