import ReverseSet
import LagGroup

namespace BB6.Agent43LagPartition
open BB6.Agent45.DelayedCarry
open BB6.Agent43ReverseSet (extract rewindSet rewindSet_sound unionBits bit_union)

structure PackedGroup where
  word : Nat
  carry : Nat
  ends : Nat
  deriving Repr, DecidableEq

structure Part where
  ancestor : Nat
  bits : Nat
  deriving Repr, DecidableEq

structure Plan where
  parent : PackedGroup
  parts : List Part
  deriving Repr, DecidableEq

def targetFast (n B i : Nat) : Nat :=
  if i<n then 0 else if (7*B).testBit (i-n) then 1 else 0

theorem targetFast_eq (n B i : Nat) : targetFast n B i=target n i B := by
  unfold targetFast target
  split
  · simp_all
  · rename_i h
    simp only [h,if_false,Nat.testBit_eq_decide_div_mod_eq]
    have hh : 7*B / 2^(i-n)%2≤1 := by omega
    by_cases he : 7*B / 2^(i-n)%2=1 <;> simp [he] <;> omega

theorem rewind_eq (n B s k c : Nat) :
    BB6.Agent43ReverseSet.rewind (fun i => n+i+3) (targetFast n B) s k c=rewind n B s k c := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    simp only [BB6.Agent43ReverseSet.rewind,rewind,predecessor,targetFast_eq,ih]

def partCheck (L n s h B : Nat) (p : Part) : Bool :=
  decide (rewindSet (fun i => n+i+3) (targetFast n B) (s+h) (n-h)
    (extract 0 p.bits L)=[p.ancestor])

def planCheck (L n s h : Nat) (p : Plan) : Bool :=
  decide (unionBits (p.parts.map Part.bits)=p.parent.ends) &&
  p.parts.all (partCheck L n s h p.parent.word)

def advancePart (L n s h : Nat) (g : PackedGroup) (p : Part) : Option PackedGroup :=
  let r := recover n g.word s h p.ancestor
  let e := fixedRun L n r.1 (s+n) p.bits h
  if e=0 then none else some ⟨r.1,p.ancestor,e⟩

def advancePlan (L n s h : Nat) (p : Plan) : List PackedGroup :=
  p.parts.filterMap (advancePart L n s h p.parent)

def next (L n s h : Nat) (ps : List Plan) : List PackedGroup :=
  ps.flatMap (advancePlan L n s h)

def Covered (n s : Nat) (gs : List PackedGroup) : Prop :=
  ∀ B a C c, Trace n s B a → Extend n s B a n C c →
    ∃ g∈gs, g.word=B ∧ g.carry=a ∧ g.ends.testBit c=true

def first (L n : Nat) : List PackedGroup :=
  [⟨1,(n+2)/2,lookahead L n 1 1 ((n+2)/2) n⟩]

theorem first_covered (L n : Nat) (hb : 2*n+3<2^L) : Covered n 1 (first L n) := by
  intro B a C c htr he
  have hprefix := covered_first n B a C c htr he
  simp only [List.mem_singleton,Prod.mk.injEq] at hprefix
  rcases hprefix with ⟨rfl,rfl⟩
  exact ⟨⟨1,(n+2)/2,lookahead L n 1 1 ((n+2)/2) n⟩,by simp [first],rfl,rfl,lookahead_sound L n 1 1 ((n+2)/2) n C c htr he (by omega) (by omega)⟩

theorem next_covered (L n s h : Nat) (gs : List PackedGroup) (ps : List Plan)
    (hs : 1≤s) (hh : h≤n) (hb : 2*n+s+h+2<2^L)
    (hparents : ps.map Plan.parent=gs) (hchecks : ps.all (planCheck L n s h)=true)
    (hcover : Covered n s gs) : Covered n (s+h) (next L n s h ps) := by
  intro B a C c htr he
  obtain ⟨D,d,hD,hpre0⟩ := trace_split n (s+h) B a s htr hs (by omega)
  have hpre : Extend n s D d h B a := by simpa using hpre0
  obtain ⟨F,f,hmid,htail0⟩ := extend_split n (s+h) B a n C c (n-h) he (by omega)
  have hshort0 := extend_append n s D d h B a (n-h) F f hpre hmid
  have hshort : Extend n s D d n F f := by simpa only [show h+(n-h)=n by omega] using hshort0
  obtain ⟨g,hg,hword,hcarry,hend⟩ := hcover D d F f hD hshort
  rw [← hparents] at hg
  obtain ⟨p,hp,hpg⟩ := List.mem_map.mp hg
  have hcheck := List.all_eq_true.mp hchecks p hp
  unfold planCheck at hcheck
  rw [Bool.and_eq_true] at hcheck
  obtain ⟨hu,hparts⟩ := hcheck
  have hu' := of_decide_eq_true hu
  rw [← hpg,← hu'] at hend
  obtain ⟨bits,hbits,hbit⟩ := bit_union _ f hend
  obtain ⟨q,hq,hqb⟩ := List.mem_map.mp hbits
  rw [← hqb] at hbit
  have hf := (trace_bounds n _ _ _ (extend_trace n s D d n F f hD hshort)).2.2.2
  have hmem : f∈extract 0 q.bits L := (BB6.Agent43ReverseSet.extract_iff _ _ _ _).2 ⟨by omega,by omega,by simpa using hbit⟩
  have hpart := of_decide_eq_true (List.all_eq_true.mp hparts q hq)
  change rewindSet (fun i => n+i+3) (targetFast n p.parent.word) (s+h) (n-h)
      (extract 0 q.bits L)=[q.ancestor] at hpart
  have hrev := rewindSet_sound (fun i => n+i+3) (targetFast n p.parent.word) (s+h) (n-h) f _ hmem
  rw [hpart,rewind_eq,List.mem_singleton,hpg,hword] at hrev
  have hactual := rewind_exact n s D d h B a (n-h) F f hD hpre hmid (by omega)
  have ha : q.ancestor=a := by omega
  have hr := recover_exact n s D d h B a hD hpre hh
  have htail : Extend n ((s+h)+(n-h)) F f h C c := by simpa only [show n-(n-h)=h by omega] using htail0
  have he' := fixedRun_suffix_sound L n (s+h) B a (n-h) F f h C c q.bits htr hmid htail (by omega) (by omega) hbit
  have hidx : s+h+(n-h)=s+n := by omega
  rw [hidx] at he'
  have hnon : fixedRun L n B (s+n) q.bits h≠0 := by intro hz; simp [hz] at he'
  refine ⟨⟨B,a,fixedRun L n B (s+n) q.bits h⟩,List.mem_flatMap.mpr ⟨p,hp,?_⟩,rfl,rfl,he'⟩
  unfold advancePlan
  apply List.mem_filterMap.mpr
  refine ⟨q,hq,?_⟩
  simp [advancePart,hpg,hword,ha,hr,hnon]

theorem to_covered (n s : Nat) (gs : List PackedGroup) (h : Covered n s gs) :
    BB6.Agent45.DelayedCarry.Covered n s (gs.map fun g => (g.word,g.carry)) := by
  intro B a C c htr he
  obtain ⟨g,hg,hw,hc,_⟩ := h B a C c htr he
  exact List.mem_map.mpr ⟨g,hg,by simp [hw,hc]⟩

structure PackedCert (n K s : Nat) (gs : List PackedGroup) : Prop where
  cover : Covered n s gs
  margins : ∀ j, 1≤j → j≤s → LateMargin n K j

theorem cert_first_packed (L n K : Nat) (hb : 2*n+3<2^L)
    (hgood : MarginOK n K 1 0 [(1,(n+2)/2)]=true) : PackedCert n K 1 (first L n) :=
  ⟨first_covered L n hb,(cert_first n K hgood).margins⟩

theorem cert_next_packed (L n K s h : Nat) (gs : List PackedGroup) (ps : List Plan)
    (hs : 1≤s) (hh : h≤n) (hb : 2*n+s+h+2<2^L)
    (hparents : ps.map Plan.parent=gs) (hchecks : ps.all (planCheck L n s h)=true)
    (hc : PackedCert n K s gs)
    (hgood : MarginOK n K s h (gs.map fun g => (g.word,g.carry))=true) :
    PackedCert n K (s+h) (next L n s h ps) := by
  refine ⟨next_covered L n s h gs ps hs hh hb hparents hchecks hc.cover,?_⟩
  intro j hj hjs
  by_cases hle : j≤s
  · exact hc.margins j hj hle
  · exact margin_block n K s h j _ hs (by omega) hjs (to_covered n s gs hc.cover) hgood

theorem cert_empty_packed (n K s : Nat) (h : PackedCert n K s []) : Cert n K s [] :=
  ⟨to_covered n s [] h.cover,h.margins⟩

#print axioms next_covered
#print axioms cert_next_packed
#print axioms cert_empty_packed
end BB6.Agent43LagPartition
