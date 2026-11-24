import BitExact
import BitGroupCert
namespace BB6.Agent28ForwardImage
open BB6.Agent28BitCarry BB6.Agent28BitExact BB6.Agent28BitGroup BB6.Agent45.DelayedCarry

theorem lagStep_complete (L weight y bits c : Nat) (h : (lagStep L weight y bits).testBit c=true) :
    ∃ a x, bits.testBit a=true ∧ x≤1 ∧ 2*c+y=a+x*weight := by
  have hc := packEven_below L _ c h
  have hh := packEven_complete L _ c hc h
  simp only [Nat.testBit_shiftRight,Nat.testBit_or,Bool.or_eq_true] at hh
  rcases hh with h1|h2
  · exact ⟨y+2*c,0,h1,by omega,by omega⟩
  · rw [Nat.testBit_shiftLeft,Bool.and_eq_true] at h2
    have hle : weight≤y+2*c := of_decide_eq_true h2.1
    exact ⟨y+2*c-weight,1,h2.2,by omega,by omega⟩

def BoundedAt (n i bits : Nat) : Prop := ∀ c, bits.testBit c=true → c≤n+i+2

theorem lagStep_bounded (L n B i bits : Nat) (hb : BoundedAt n i bits) :
    BoundedAt n (i+1) (lagStep L (n+i+3) (target n i B) bits) := by
  intro c hc
  obtain ⟨a,x,ha,hx,he⟩ := lagStep_complete L _ _ _ _ hc
  have ha' := hb a ha
  have hh := Nat.mul_le_mul_right (n+i+3) hx
  simp only [Nat.one_mul] at hh
  omega

theorem fixedRun_bounded (L n B i bits k : Nat) (hb : BoundedAt n i bits) :
    BoundedAt n (i+k) (fixedRun L n B i bits k) := by
  induction k generalizing i bits with
  | zero => exact hb
  | succ k ih =>
    by_cases hz : bits=0
    · simp [hz,fixedRun_zero,BoundedAt]
    · rw [fixedRun,ite_eq_right hz]
      simpa only [Nat.add_assoc,Nat.add_comm 1 k] using ih (i+1) _ (lagStep_bounded L n B i bits hb)

theorem fixedRun_rewind_mem (L n B i bits k c : Nat) (hb : BoundedAt n i bits)
    (hc : (fixedRun L n B i bits k).testBit c=true) :
    bits.testBit (rewind n B i k c)=true := by
  induction k generalizing c with
  | zero => exact hc
  | succ k ih =>
    rw [fixedRun_add] at hc
    simp only [fixedRun] at hc
    split at hc
    · simp at hc
    · obtain ⟨a,x,ha,hx,he⟩ := lagStep_complete L _ _ _ _ hc
      have hab := fixedRun_bounded L n B i bits k hb a ha
      obtain ⟨hp,_⟩ := inverse_digit (n+(i+k)+3) a x c (target n (i+k) B) (by omega) (by omega) he
      simpa only [rewind,predecessor,hp] using ih a ha

theorem fixedRun_rewind_single (L n B i a k c : Nat) (ha : a≤n+i+2)
    (hc : (fixedRun L n B i (2^a) k).testBit c=true) : rewind n B i k c=a := by
  have hb : BoundedAt n i (2^a) := by
    intro d hd
    rw [Nat.testBit_two_pow] at hd
    have he : a=d := of_decide_eq_true hd
    omega
  have hh := fixedRun_rewind_mem L n B i (2^a) k c hb hc
  rw [Nat.testBit_two_pow] at hh
  exact (of_decide_eq_true hh).symm

/-- Untrusted candidate at the new low-prefix boundary, together with a
    forward image through the remaining part of the previous window. -/
structure ImageSplit where
  word : Nat
  carry : Nat
  image : Nat
  deriving Repr, DecidableEq

def ImagePlan := BitGroup × List ImageSplit

def imageUnion : List ImageSplit → Nat
  | [] => 0
  | p::ps => p.image ||| imageUnion ps

theorem imageUnion_member (ps : List ImageSplit) (c : Nat)
    (h : (imageUnion ps).testBit c=true) : ∃ p∈ps, p.image.testBit c=true := by
  induction ps with
  | nil => simp [imageUnion] at h
  | cons p ps ih =>
    simp only [imageUnion,Nat.testBit_or,Bool.or_eq_true] at h
    rcases h with h|h
    · exact ⟨p,List.mem_cons_self,h⟩
    · obtain ⟨q,hq,hb⟩ := ih h
      exact ⟨q,List.mem_cons_of_mem p hq,hb⟩

def ImageOK (L n s h : Nat) (g : BitGroup) (ps : List ImageSplit) : Prop :=
  g.ends &&& imageUnion ps=g.ends ∧
  ∀ p∈ps, p.carry≤n+s+h+2 ∧
    p.image=fixedRun L n g.word (s+h) (2^p.carry) (n-h) ∧
    recover n g.word s h p.carry=(p.word,g.carry)

def checkImage (L n s h : Nat) (g : BitGroup) (p : ImageSplit) : Bool :=
  decide (p.carry≤n+s+h+2 ∧
    p.image=fixedRun L n g.word (s+h) (2^p.carry) (n-h) ∧
    recover n g.word s h p.carry=(p.word,g.carry))

def checkImagePlan (L n s h : Nat) (gp : ImagePlan) : Bool :=
  decide (gp.1.ends &&& imageUnion gp.2=gp.1.ends) && gp.2.all (checkImage L n s h gp.1)

theorem checkImagePlan_sound (L n s h : Nat) (plans : List ImagePlan)
    (hc : plans.all (checkImagePlan L n s h)=true) : ∀ gp∈plans, ImageOK L n s h gp.1 gp.2 := by
  intro gp hg
  have he := List.all_eq_true.mp hc gp hg
  simp only [checkImagePlan,Bool.and_eq_true] at he
  exact ⟨of_decide_eq_true he.1,fun p hp => of_decide_eq_true (List.all_eq_true.mp he.2 p hp)⟩

def imageNextSplit (L n s h : Nat) (g : BitGroup) (p : ImageSplit) : BitGroup :=
  ⟨p.word,p.carry,fixedRun L n p.word (s+n) (g.ends &&& p.image) h⟩

def imageNext (L n s h : Nat) (plans : List ImagePlan) : List BitGroup :=
  plans.flatMap fun gp => (gp.2.map (imageNextSplit L n s h gp.1)).filter (fun g => g.ends != 0)

theorem image_next_covered (L n s h : Nat) (plans : List ImagePlan) (hs : 1≤s) (hh : h≤n)
    (hb : 2*n+s+h+2<2^L) (hcover : BitCovered n s (plans.map Prod.fst))
    (hparts : ∀ gp∈plans, ImageOK L n s h gp.1 gp.2) :
    BitCovered n (s+h) (imageNext L n s h plans) := by
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
  have hbUnion : (imageUnion gp.2).testBit f=true := by
    have hu := congrArg (fun b : Nat => b.testBit f) hunion
    simpa [Nat.testBit_and,hend] using hu
  obtain ⟨p,hp,hpbit⟩ := imageUnion_member gp.2 f hbUnion
  obtain ⟨hbound,himage,hrecover⟩ := hcheck p hp
  have him : (fixedRun L n D (s+h) (2^p.carry) (n-h)).testBit f=true := by rwa [himage,hword] at hpbit
  have hr1 := fixedRun_rewind_single L n D (s+h) p.carry (n-h) f (by omega) him
  have hr2 := rewind_exact n s D d h B a (n-h) F f hD hpre hmid (by omega)
  have ha : p.carry=a := hr1.symm.trans hr2
  have hr := recover_exact n s D d h B a hD hpre hh
  rw [hword,ha,hr,hcarry] at hrecover
  have hpword : p.word=B := (congrArg Prod.fst hrecover).symm
  have htail : Extend n ((s+h)+(n-h)) F f h C c := by simpa only [show n-(n-h)=h by omega] using htail0
  have hinter : (g.ends &&& p.image).testBit f=true := by simp [Nat.testBit_and,hend,hpbit]
  have hbit := fixedRun_suffix_sound L n (s+h) B a (n-h) F f h C c (g.ends &&& p.image) htr hmid htail (by omega) (by omega) hinter
  have hidx : s+h+(n-h)=s+n := by omega
  rw [hidx,← hpword,← hgEq] at hbit
  have hnon : fixedRun L n p.word (s+n) (gp.1.ends &&& p.image) h ≠ 0 := by
    intro hz; rw [hz] at hbit; simp at hbit
  refine ⟨imageNextSplit L n s h gp.1 p,List.mem_flatMap.mpr ⟨gp,hgp,?_⟩,hpword,ha,hbit⟩
  simp only [List.mem_filter]
  exact ⟨List.mem_map.mpr ⟨p,hp,rfl⟩,by simpa [imageNextSplit] using hnon⟩

theorem image_cert_next (L n K s h : Nat) (plans : List ImagePlan) (hs : 1≤s) (hh : h≤n)
    (hb : 2*n+s+h+2<2^L) (hc : BitCert n K s (plans.map Prod.fst))
    (hparts : ∀ gp∈plans, ImageOK L n s h gp.1 gp.2)
    (hgood : MarginOK n K s h ((plans.map Prod.fst).map fun g => (g.word,g.carry))=true) :
    BitCert n K (s+h) (imageNext L n s h plans) := by
  refine ⟨image_next_covered L n s h plans hs hh hb hc.cover hparts,?_⟩
  intro j hj hjs
  by_cases hle : j≤s
  · exact hc.margins j hj hle
  · exact margin_block n K s h j _ hs (by omega) hjs (covered_of_bits n s _ hc.cover) hgood

#print axioms image_next_covered
#print axioms image_cert_next
#print axioms lagStep_complete
#print axioms fixedRun_rewind_single
end BB6.Agent28ForwardImage
