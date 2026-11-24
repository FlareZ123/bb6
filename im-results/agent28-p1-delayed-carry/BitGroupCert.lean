import BitSpread
import LagGroup
namespace BB6.Agent28BitGroup
open BB6.Agent45.DelayedCarry
open BB6.Agent28BitSpread

/-- The bitset image of a set of endpoints under the deterministic
    predecessor map, in reverse chronological order. -/
def backRun (L n B s : Nat) : Nat → Nat → Nat
  | 0,bits => bits
  | k+1,bits => backRun L n B s k
      (reverseStep L (n+s+k+3) (target n (s+k) B) bits)

theorem backRun_add (L n B s k j bits : Nat) :
    backRun L n B s (k+j) bits =
      backRun L n B s k (backRun L n B (s+k) j bits) := by
  induction j generalizing bits with
  | zero => rfl
  | succ j ih =>
    rw [show k+(j+1)=(k+j)+1 by omega]
    change backRun L n B s (k+j) (reverseStep L (n+s+(k+j)+3) (target n (s+(k+j)) B) bits) =
      backRun L n B s k (backRun L n B (s+k) j (reverseStep L (n+(s+k)+j+3) (target n ((s+k)+j) B) bits))
    rw [ih]
    simp only [Nat.add_assoc]

theorem backRun_suffix_sound (L n s B a h D d j C c bits : Nat)
    (htr : Trace n s B a) (hpre : Extend n s B a h D d)
    (hsuf : Extend n (s+h) D d j C c) (hj : h+j≤n)
    (hb : n+s+h+j+2<2^L) (hbit : bits.testBit c=true) :
    (backRun L n B (s+h) j bits).testBit d=true := by
  induction hsuf generalizing bits with
  | nil => exact hbit
  | step k C c x e hsuf hx hEq ih =>
    have hfull := extend_append n s B a h D d k C c hpre hsuf
    have htrace := extend_trace n s B a (h+k) C c htr hfull
    have hc := (trace_bounds n _ _ _ htrace).2.2.2
    obtain ⟨R,hR⟩ := extend_mod n s B a (h+k) C c hfull
    have hy := target_prefix n s (s+h+k) B R (by omega)
    rw [← hR] at hy
    have heq : 2*e+target n (s+h+k) B=c+x*(n+(s+h+k)+3) := by
      rw [← hy]; exact hEq
    have hCe : 0<n+(s+h+k)+3 := by omega
    have hcb : c<n+(s+h+k)+3 := by omega
    have hprod : x*(n+(s+h+k)+3)≤n+(s+h+k)+3 := by
      simpa using Nat.mul_le_mul_right (n+(s+h+k)+3) hx
    have hE : 2*e+target n (s+h+k) B<2*(n+(s+h+k)+3) := by omega
    have hEb : e<2^L := by omega
    obtain ⟨hp,_⟩ := inverse_digit (n+(s+h+k)+3) c x e (target n (s+h+k) B) hCe hcb heq
    have hrev := reverseStep_sound L (n+(s+h+k)+3) (target n (s+h+k) B) bits e hCe hEb hE hbit
    rw [hp] at hrev
    have hrev' : (reverseStep L (n+(s+h)+k+3) (target n ((s+h)+k) B) bits).testBit c=true := by
      simpa only [Nat.add_assoc] using hrev
    exact ih _ (by omega) (by omega) hrev'

structure BitGroup where
  word : Nat
  carry : Nat
  ends : Nat
  deriving Repr, DecidableEq

def BitCovered (n s : Nat) (gs : List BitGroup) : Prop :=
  ∀ B a C c, Trace n s B a → Extend n s B a n C c →
    ∃ g∈gs, g.word=B ∧ g.carry=a ∧ g.ends.testBit c=true

def bitFirst (L n : Nat) : List BitGroup :=
  [⟨1,(n+2)/2,lookahead L n 1 1 ((n+2)/2) n⟩]

theorem bit_first_covered (L n : Nat) (hb : 2*n+3<2^L) : BitCovered n 1 (bitFirst L n) := by
  intro B a C c htr he
  have hprefix := covered_first n B a C c htr he
  simp only [List.mem_singleton,Prod.mk.injEq] at hprefix
  rcases hprefix with ⟨rfl,rfl⟩
  exact ⟨_,List.mem_singleton_self _,rfl,rfl,lookahead_sound L n 1 1 ((n+2)/2) n C c htr he (by omega) (by omega)⟩

/-- A proposed partition of an endpoint set. Each record stores the
    proposed low-prefix word and carry at the new split, and all endpoints
    at the old window's end that are assigned to it. -/
structure Split where
  word : Nat
  carry : Nat
  ends : Nat
  deriving Repr, DecidableEq

def splitUnion : List Split → Nat
  | [] => 0
  | p::ps => p.ends ||| splitUnion ps

theorem splitUnion_member (ps : List Split) (c : Nat) (h : (splitUnion ps).testBit c=true) :
    ∃ p∈ps, p.ends.testBit c=true := by
  induction ps with
  | nil => simp [splitUnion] at h
  | cons p ps ih =>
    simp only [splitUnion,Nat.testBit_or,Bool.or_eq_true] at h
    rcases h with h|h
    · exact ⟨p,List.mem_cons_self,h⟩
    · obtain ⟨q,hq,hb⟩ := ih h
      exact ⟨q,List.mem_cons_of_mem p hq,hb⟩

/-- The only trusted requirements on a proposed partition: coverage of all
    old endpoint bits; a singleton reverse image; exact recovery of the new
    prefix word. Extra endpoints and overlapping parts are harmless. -/
def PartitionOK (L n s h : Nat) (g : BitGroup) (ps : List Split) : Prop :=
  g.ends &&& splitUnion ps = g.ends ∧
  ∀ p∈ps, backRun L n g.word (s+h) (n-h) p.ends=2^p.carry ∧
    recover n g.word s h p.carry=(p.word,g.carry)

def PartPlan := BitGroup × List Split

def checkSplit (L n s h : Nat) (g : BitGroup) (p : Split) : Bool :=
  decide (backRun L n g.word (s+h) (n-h) p.ends=2^p.carry ∧
    recover n g.word s h p.carry=(p.word,g.carry))

def checkPartition (L n s h : Nat) (gp : PartPlan) : Bool :=
  decide (gp.1.ends &&& splitUnion gp.2=gp.1.ends) &&
    gp.2.all (checkSplit L n s h gp.1)

theorem checkPartition_sound (L n s h : Nat) (gp : PartPlan)
    (hcheck : checkPartition L n s h gp=true) : PartitionOK L n s h gp.1 gp.2 := by
  simp only [checkPartition, Bool.and_eq_true] at hcheck
  exact ⟨of_decide_eq_true hcheck.1, fun p hp => of_decide_eq_true (List.all_eq_true.mp hcheck.2 p hp)⟩

theorem checkPlan_sound (L n s h : Nat) (plans : List PartPlan)
    (hc : plans.all (checkPartition L n s h)=true) :
    ∀ gp∈plans, PartitionOK L n s h gp.1 gp.2 :=
  fun gp hg => checkPartition_sound L n s h gp (List.all_eq_true.mp hc gp hg)

def nextSplit (L n s h : Nat) (p : Split) : BitGroup :=
  ⟨p.word,p.carry,fixedRun L n p.word (s+n) p.ends h⟩

def bitNext (L n s h : Nat) (plans : List PartPlan) : List BitGroup :=
  plans.flatMap fun gp => (gp.2.map (nextSplit L n s h)).filter (fun g => g.ends != 0)

theorem bit_next_covered (L n s h : Nat) (plans : List PartPlan) (hs : 1≤s) (hh : h≤n)
    (hb : 2*n+s+h+2<2^L) (hcover : BitCovered n s (plans.map Prod.fst))
    (hparts : ∀ gp∈plans, PartitionOK L n s h gp.1 gp.2) :
    BitCovered n (s+h) (bitNext L n s h plans) := by
  intro B a C c htr he
  obtain ⟨D,d,hD,hpre0⟩ := trace_split n (s+h) B a s htr hs (by omega)
  have hpre : Extend n s D d h B a := by simpa using hpre0
  obtain ⟨F,f,hmid,htail0⟩ := extend_split n (s+h) B a n C c (n-h) he (by omega)
  have hshort0 := extend_append n s D d h B a (n-h) F f hpre hmid
  have hshort : Extend n s D d n F f := by simpa only [show h+(n-h)=n by omega] using hshort0
  obtain ⟨g,hg,hword,hcarry,hend⟩ := hcover D d F f hD hshort
  obtain ⟨gp,hgp,hgEq⟩ := List.mem_map.mp hg
  have hpart := hparts gp hgp
  rw [hgEq] at hpart
  obtain ⟨hunion,hcheck⟩ := hpart
  have hbUnion : (splitUnion gp.2).testBit f=true := by
    have hu := congrArg (fun b : Nat => b.testBit f) hunion
    simpa [Nat.testBit_and,hend] using hu
  obtain ⟨p,hp,hpbit⟩ := splitUnion_member gp.2 f hbUnion
  obtain ⟨hback,hrecover⟩ := hcheck p hp
  have hrev := backRun_suffix_sound L n s D d h B a (n-h) F f p.ends hD hpre hmid (by omega) (by omega) hpbit
  rw [← hword,hback,Nat.testBit_two_pow] at hrev
  have ha : p.carry=a := of_decide_eq_true hrev
  have hr := recover_exact n s D d h B a hD hpre hh
  rw [hword,ha,hr,hcarry] at hrecover
  have hpword : p.word=B := (congrArg Prod.fst hrecover).symm
  have htail : Extend n ((s+h)+(n-h)) F f h C c := by simpa only [show n-(n-h)=h by omega] using htail0
  have hbit := fixedRun_suffix_sound L n (s+h) B a (n-h) F f h C c p.ends htr hmid htail (by omega) (by omega) hpbit
  have hidx : s+h+(n-h)=s+n := by omega
  rw [hidx,← hpword] at hbit
  have hnon : fixedRun L n p.word (s+n) p.ends h ≠ 0 := by
    intro hz; rw [hz] at hbit; simp at hbit
  refine ⟨nextSplit L n s h p,List.mem_flatMap.mpr ⟨gp,hgp,?_⟩,hpword,ha,hbit⟩
  simp only [List.mem_filter]
  exact ⟨List.mem_map.mpr ⟨p,hp,rfl⟩,by simpa [nextSplit] using hnon⟩

theorem covered_of_bits (n s : Nat) (gs : List BitGroup) (h : BitCovered n s gs) :
    Covered n s (gs.map fun g => (g.word,g.carry)) := by
  intro B a C c htr he
  obtain ⟨g,hg,hw,hc,_⟩ := h B a C c htr he
  exact List.mem_map.mpr ⟨g,hg,by simp [hw,hc]⟩

structure BitCert (n K s : Nat) (gs : List BitGroup) : Prop where
  cover : BitCovered n s gs
  margins : ∀ j, 1≤j → j≤s → LateMargin n K j

theorem bit_cert_first (L n K : Nat) (hb : 2*n+3<2^L)
    (hgood : MarginOK n K 1 0 [(1,(n+2)/2)]=true) : BitCert n K 1 (bitFirst L n) :=
  ⟨bit_first_covered L n hb,(cert_first n K hgood).margins⟩

theorem bit_cert_next (L n K s h : Nat) (plans : List PartPlan) (hs : 1≤s) (hh : h≤n)
    (hb : 2*n+s+h+2<2^L) (hc : BitCert n K s (plans.map Prod.fst))
    (hparts : ∀ gp∈plans, PartitionOK L n s h gp.1 gp.2)
    (hgood : MarginOK n K s h ((plans.map Prod.fst).map fun g => (g.word,g.carry))=true) :
    BitCert n K (s+h) (bitNext L n s h plans) := by
  refine ⟨bit_next_covered L n s h plans hs hh hb hc.cover hparts,?_⟩
  intro j hj hjs
  by_cases hle : j≤s
  · exact hc.margins j hj hle
  · exact margin_block n K s h j _ hs (by omega) hjs (covered_of_bits n s _ hc.cover) hgood

theorem bit_cert_empty (n K s : Nat) (h : BitCert n K s []) : Cert n K s [] :=
  ⟨covered_of_bits n s [] h.cover,h.margins⟩

#print axioms backRun_suffix_sound
#print axioms bit_next_covered
#print axioms bit_cert_next
#print axioms bit_cert_empty
end BB6.Agent28BitGroup
