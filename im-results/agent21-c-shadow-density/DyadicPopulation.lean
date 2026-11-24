import DyadicAmplification

namespace BB6.Agent21Dyadic

-- Words in the population are reversed, so the last gap is the head.
def rcost (w : List Nat) := cost w.reverse
def rpos (w : List Nat) := Positive w.reverse
def rnum (a : Affine) (w : List Nat) (b : Int) := numer a w.reverse b

theorem rcost_cons (r : Nat) (w : List Nat) : rcost (r::w)=rcost w+r := by
  simp [rcost,List.reverse_cons,cost_append,cost]

theorem rpos_cons (r : Nat) (w : List Nat) : rpos (r::w) ↔ 0<r ∧ rpos w := by
  unfold rpos Positive
  simp [List.reverse_cons,List.mem_append]
  constructor
  · intro h
    exact ⟨h r (Or.inr rfl),fun x hx => h x (Or.inl hx)⟩
  · intro h x hx
    rcases hx with hx|hx
    · exact h.2 x hx
    · simpa [hx] using h.1

theorem rnum_cons (a : Affine) (r : Nat) (w : List Nat) (b : Int) :
    rnum a (r::w) b=rnum a w b+P (rcost w)*offset (mass a b+drift w.reverse) r := by
  unfold rnum rcost numer
  rw [List.reverse_cons,acc_append]
  simp [acc]
  omega

theorem offset_extend (S : Int) (r : Nat) : offset S (r+2)=offset S r := by
  unfold offset parity shift
  push_cast
  omega

theorem rnum_extend (a : Affine) (r : Nat) (w : List Nat) (b : Int) :
    rnum a ((r+2)::w) b=rnum a (r::w) b := by
  rw [rnum_cons,rnum_cons,offset_extend]

def shiftBit (n : Nat) (b : Int) (e : Bool) := b+if e then P n else 0

def passes (a : Affine) (n : Nat) (b : Int) (w : List Nat) : Bool := (rnum a w b)%P n==0

theorem passes_iff (a : Affine) (n : Nat) (b : Int) (w : List Nat) :
    passes a n b w=true ↔ P n∣rnum a w b := by
  simp [passes,Int.dvd_iff_emod_eq_zero]

theorem rnum_bit (a : Affine) (n : Nat) (b : Int) (w : List Nat) (h : Good a) :
    rnum a w (shiftBit n b true)=rnum a w b+P n*slope a w.reverse := by
  unfold rnum shiftBit
  simp only [if_true]
  rw [numer_affine _ _ _ h,numer_affine _ _ _ h,Int.mul_add,Int.mul_comm (slope a w.reverse) (P n)]
  omega

theorem bit_unique (a : Affine) (n : Nat) (b : Int) (w : List Nat) (h : Good a) :
    ¬(passes a (n+1) (shiftBit n b false) w=true ∧ passes a (n+1) (shiftBit n b true) w=true) := by
  intro ⟨h0,h1⟩
  rw [passes_iff] at h0 h1
  simp [shiftBit] at h0
  rw [rnum_bit _ _ _ _ h] at h1
  have hd := Int.dvd_sub h1 h0
  rw [show rnum a w b+P n*slope a w.reverse-rnum a w b=P n*slope a w.reverse by omega,P_add] at hd
  have he := (Int.mul_dvd_mul_iff_left (P_ne n)).mp hd
  have ho := slope_odd a w.reverse h
  change 2∣slope a w.reverse at he
  have hm := Int.emod_eq_zero_of_dvd he
  omega

theorem bit_down (a : Affine) (n : Nat) (b : Int) (e : Bool) (w : List Nat) (h : Good a)
    (hp : P n∣rnum a w (shiftBit n b e)) : P n∣rnum a w b := by
  cases e
  · simpa [shiftBit] using hp
  · rw [rnum_bit _ _ _ _ h] at hp
    have hd := Int.dvd_sub hp (Int.dvd_mul_right (P n) (slope a w.reverse))
    simpa using hd

theorem bit_exists (a : Affine) (n : Nat) (b : Int) (w : List Nat) (h : Good a)
    (hp : P n∣rnum a w b) : ∃ e : Bool, passes a (n+1) (shiftBit n b e) w=true := by
  obtain ⟨q,hq⟩ := hp
  by_cases he : q%2=0
  · refine ⟨false,(passes_iff _ _ _ _).mpr ?_⟩
    simp [shiftBit]
    rw [hq,P_add]
    apply (Int.mul_dvd_mul_iff_left (P_ne n)).mpr
    exact Int.dvd_of_emod_eq_zero he
  · refine ⟨true,(passes_iff _ _ _ _).mpr ?_⟩
    rw [rnum_bit _ _ _ _ h,hq,←Int.mul_add,P_add]
    apply (Int.mul_dvd_mul_iff_left (P_ne n)).mpr
    apply Int.dvd_of_emod_eq_zero
    have ho := slope_odd a w.reverse h
    change (q+slope a w.reverse)%2=0
    omega

structure Pop where
  c : List (List Nat)
  p : List (List Nat)
  deriving Repr

def extendLast : List Nat → Option (List Nat)
  | [] => none
  | r::w => some ((r+2)::w)

def step (a : Affine) (n : Nat) (b : Int) (Q : Pop) (e : Bool) : Pop :=
  let check := passes a (n+1) (shiftBit n b e)
  ⟨((Q.c.map (1::·))++Q.p).filter check,
   ((Q.c.map (2::·))++Q.c.filterMap extendLast).filter check⟩

def Cspec (a : Affine) (n : Nat) (b : Int) (w : List Nat) : Prop :=
  rpos w ∧ rcost w=n ∧ P n∣rnum a w b

def Aspec (a : Affine) (n : Nat) (b : Int) (w : List Nat) : Prop :=
  (∃ r v, w=r::v ∧ 2≤r) ∧ rpos w ∧ rcost w=n+1 ∧ P n∣rnum a w b

def ValidPop (a : Affine) (n : Nat) (b : Int) (Q : Pop) : Prop :=
  (∀ w, w∈Q.c ↔ Cspec a n b w) ∧ (∀ w, w∈Q.p ↔ Aspec a n b w)

theorem initial_valid (a : Affine) : ValidPop a 0 0 ⟨[[]],[]⟩ := by
  constructor
  · intro w
    cases w with
    | nil => simp [Cspec,rpos,rcost,Positive,cost,P]
    | cons r w =>
      simp only [Cspec,rpos_cons,rcost_cons,List.mem_singleton,List.cons_ne_nil,false_iff,not_and]
      intro h hc
      omega
  · intro w
    simp only [List.not_mem_nil,false_iff]
    intro ⟨⟨r,v,hw,hr⟩,hp,hc,hd⟩
    subst w
    rw [rcost_cons] at hc
    omega

theorem prefix_dvd (a : Affine) (r : Nat) (w : List Nat) (b : Int)
    (h : P (rcost w)∣rnum a (r::w) b) : P (rcost w)∣rnum a w b := by
  rw [rnum_cons] at h
  have h' := Int.dvd_sub h (Int.dvd_mul_right (P (rcost w)) (offset (mass a b+drift w.reverse) r))
  simpa using h'

theorem step_valid (a : Affine) (n : Nat) (b : Int) (Q : Pop) (e : Bool) (h : Good a)
    (hv : ValidPop a n b Q) : ValidPop a (n+1) (shiftBit n b e) (step a n b Q e) := by
  constructor
  · intro w
    simp only [step,List.mem_filter,List.mem_append,List.mem_map,passes_iff,Cspec]
    constructor
    · intro ⟨hw,hd⟩
      rcases hw with ⟨v,hv',rfl⟩|hw
      · obtain ⟨hp,hc,_⟩ := (hv.1 v).mp hv'
        exact ⟨(rpos_cons _ _).mpr ⟨by decide,hp⟩,by rw [rcost_cons,hc],hd⟩
      · obtain ⟨_,hp,hc,_⟩ := (hv.2 w).mp hw
        exact ⟨hp,hc,hd⟩
    · intro ⟨hp,hc,hd⟩
      refine ⟨?_,hd⟩
      cases w with
      | nil => simp [rcost,cost] at hc
      | cons r v =>
        have hpos := (rpos_cons _ _).mp hp
        by_cases hr : r=1
        · subst r
          left
          refine ⟨v,(hv.1 v).mpr ⟨hpos.2,?_,?_⟩,rfl⟩
          · rw [rcost_cons] at hc; omega
          · have hvc : rcost v=n := by rw [rcost_cons] at hc; omega
            apply bit_down a n b e v h
            have h1 := Int.dvd_trans (P_dvd n (n+1) (by omega)) hd
            rw [←hvc] at h1 ⊢
            exact prefix_dvd a 1 v _ h1
        · right
          apply (hv.2 (r::v)).mpr
          exact ⟨⟨r,v,rfl,by omega⟩,hp,hc,bit_down a n b e _ h (Int.dvd_trans (P_dvd n (n+1) (by omega)) hd)⟩
  · intro w
    simp only [step,List.mem_filter,List.mem_append,List.mem_map,List.mem_filterMap,passes_iff,Aspec]
    constructor
    · intro ⟨hw,hd⟩
      rcases hw with ⟨v,hv',rfl⟩|⟨v,hv',he⟩
      · obtain ⟨hp,hc,_⟩ := (hv.1 v).mp hv'
        exact ⟨⟨2,v,rfl,by decide⟩,(rpos_cons _ _).mpr ⟨by decide,hp⟩,by rw [rcost_cons,hc],hd⟩
      · cases v with
        | nil => simp [extendLast] at he
        | cons r v =>
          simp [extendLast] at he
          subst w
          obtain ⟨hp,hc,_⟩ := (hv.1 (r::v)).mp hv'
          rw [rcost_cons] at hc
          exact ⟨⟨r+2,v,rfl,by omega⟩,(rpos_cons _ _).mpr ⟨by omega,((rpos_cons _ _).mp hp).2⟩,by rw [rcost_cons]; omega,hd⟩
    · intro ⟨⟨r,v,heq,hr⟩,hp,hc,hd⟩
      subst w
      refine ⟨?_,hd⟩
      by_cases he : r=2
      · subst r
        left
        refine ⟨v,(hv.1 v).mpr ⟨((rpos_cons _ _).mp hp).2,?_,?_⟩,rfl⟩
        · rw [rcost_cons] at hc; omega
        · have hvc : rcost v=n := by rw [rcost_cons] at hc; omega
          apply bit_down a n b e v h
          have h1 := Int.dvd_trans (P_dvd n (n+1) (by omega)) hd
          rw [←hvc] at h1 ⊢
          exact prefix_dvd a 2 v _ h1
      · right
        have hr' : r-2+2=r := by omega
        refine ⟨(r-2)::v,(hv.1 ((r-2)::v)).mpr ⟨?_,?_,?_⟩,by simp [extendLast,hr']⟩
        · exact (rpos_cons _ _).mpr ⟨by omega,((rpos_cons _ _).mp hp).2⟩
        · rw [rcost_cons] at hc ⊢; omega
        · apply bit_down a n b e _ h
          rw [←rnum_extend a (r-2) v _,hr']
          exact Int.dvd_trans (P_dvd n (n+1) (by omega)) hd

def weight (Q : Pop) : Nat := 2*Q.c.length+Q.p.length

private theorem filters_le {α : Type} (p q : α→Bool) (l : List α)
    (h : ∀ x, ¬(p x=true ∧ q x=true)) :
    (l.filter p).length+(l.filter q).length≤l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx := h x
    cases hp : p x <;> cases hq : q x <;> simp [List.filter_cons,hp,hq] at * <;> omega

theorem step_supermean (a : Affine) (n : Nat) (b : Int) (Q : Pop) (h : Good a) :
    weight (step a n b Q false)+weight (step a n b Q true)≤2*weight Q := by
  let L := Q.c.map (1::·)++Q.p
  let R := Q.c.map (2::·)++Q.c.filterMap extendLast
  let p := passes a (n+1) (shiftBit n b false)
  let q := passes a (n+1) (shiftBit n b true)
  have hL := filters_le p q L (fun w=>bit_unique a n b w h)
  have hR := filters_le p q R (fun w=>bit_unique a n b w h)
  have hl : L.length=Q.c.length+Q.p.length := by simp [L]
  have hr : R.length≤2*Q.c.length := by
    have hh := List.length_filterMap_le extendLast Q.c
    simp [R]
    omega
  change 2*(L.filter p).length+(R.filter p).length+ (2*(L.filter q).length+(R.filter q).length)≤2*(2*Q.c.length+Q.p.length)
  omega

structure Cylinder (a : Affine) where
  n : Nat
  b : Int
  pop : Pop
  valid : ValidPop a n b pop

def root (a : Affine) : Cylinder a := ⟨0,0,⟨[[]],[]⟩,initial_valid a⟩
def next (a : Affine) (h : Good a) (s : Cylinder a) (e : Bool) : Cylinder a :=
  ⟨s.n+1,shiftBit s.n s.b e,step a s.n s.b s.pop e,step_valid a s.n s.b s.pop e h s.valid⟩

def runBits {α : Type} (next : α→Bool→α) (s : α) : List Bool→α
  | [] => s
  | e::w => runBits next (next s e) w

theorem runBits_append {α : Type} (f : α→Bool→α) (s : α) (u v : List Bool) :
    runBits f s (u++v)=runBits f (runBits f s u) v := by
  induction u generalizing s with
  | nil => rfl
  | cons e u ih => exact ih (f s e)

theorem chooseBits (a : Affine) (h : Good a) (s : Cylinder a) (n : Nat) (t : Int)
    (ht0 : 0≤t) (ht1 : t<P n) :
    ∃ bits : List Bool, bits.length=n ∧ (runBits (next a h) s bits).n=s.n+n ∧
      (runBits (next a h) s bits).b=s.b+P s.n*t := by
  induction n generalizing s t with
  | zero =>
    have he : t=0 := by change t<1 at ht1; omega
    subst t
    exact ⟨[],rfl,by simp [runBits],by simp [runBits]⟩
  | succ n ih =>
    let e : Bool := t%2==1
    have ht : t=2*(t/2)+(if e then 1 else 0) := by
      unfold e
      by_cases hmod : t%2=1 <;> simp [hmod] <;> omega
    have hq0 : 0≤t/2 := by omega
    have hq1 : t/2<P n := by rw [P_add] at ht1; change t<P n*2 at ht1; omega
    obtain ⟨bits,hbl,hn,hb⟩ := ih (next a h s e) (t/2) hq0 hq1
    refine ⟨e::bits,by simp [hbl],?_,?_⟩
    · change (runBits (next a h) (next a h s e) bits).n=s.n+(n+1)
      rw [hn]; simp [next]; omega
    · change (runBits (next a h) (next a h s e) bits).b=s.b+P s.n*t
      rw [hb]
      change shiftBit s.n s.b e+P (s.n+1)*(t/2)=s.b+P s.n*t
      rw [P_add]; change shiftBit s.n s.b e+(P s.n*2)*(t/2)=s.b+P s.n*t
      rw [Int.mul_assoc]
      have aux (e' : Bool) (q : Int) : shiftBit s.n s.b e'+P s.n*(2*q)=s.b+P s.n*(2*q+(if e' then 1 else 0)) := by
        cases e' <;> simp [shiftBit,Int.mul_add] <;> omega
      rw [aux,←ht]

private theorem nodup_map_inj {α β : Type} (f : α→β) (l : List α)
    (hinj : ∀ x y, f x=f y→x=y) (hl : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons,List.nodup_cons] at *
    refine ⟨?_,ih hl.2⟩
    intro hm
    obtain ⟨y,hy,he⟩ := List.mem_map.mp hm
    exact hl.1 (hinj y x he ▸ hy)

theorem amplify_completed (a : Affine) (h : Good a) (s : Cylinder a) (w : List Nat)
    (hw : w∈s.pop.c) (k : Nat) :
    ∃ bits : List Bool, bits.length≤F k ∧
      2^k≤(runBits (next a h) s bits).pop.c.length := by
  obtain ⟨hp,hc,hd⟩ := (s.valid.1 w).mp hw
  have hcomp : Compatible a w.reverse s.b := by unfold Compatible; change P (rcost w)∣rnum a w s.b; rwa [hc]
  let a1 := follow a w.reverse s.b
  have hg : Good a1 := follow_good _ _ _ h
  obtain ⟨n,hn,W,hW⟩ := amplify k a1 hg
  obtain ⟨bits,hbl,hdepth,hprefix⟩ := chooseBits a h s n W.b W.lo W.hi
  let s' := runBits (next a h) s bits
  let L := W.words.map (fun v=>(w.reverse++v).reverse)
  have hnodup : L.Nodup := nodup_map_inj _ _ (by
    intro u v he
    have he' := congrArg List.reverse he
    simpa using he') W.nodup
  have hsub : L ⊆ s'.pop.c := by
    intro u hu
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hu
    obtain ⟨hvp,hvc,hvd⟩ := W.correct v hv
    apply (s'.valid.1 _).mpr
    refine ⟨?_,?_,?_⟩
    · simpa [rpos] using positive_append _ _ hp hvp
    · simp [rcost,cost_append,hvc]
      change rcost w+n=s'.n
      rw [hc,hdepth]
    · have hh := append_compatible a w.reverse v s.b W.b h hcomp hvd
      unfold Compatible at hh
      change P (cost (w.reverse++v))∣numer a (w.reverse++v) (s.b+P (rcost w)*W.b) at hh
      rw [cost_append,hvc] at hh
      change P (rcost w+n)∣numer a (w.reverse++v) (s.b+P (rcost w)*W.b) at hh
      rw [hc] at hh
      simpa [rnum,hdepth,hprefix,s'] using hh
  have hle := hnodup.length_le_of_subset hsub
  have hlen : L.length=W.words.length := by simp [L]
  refine ⟨bits,by omega,?_⟩
  change 2^k≤s'.pop.c.length
  omega

theorem pow_ge_self (k : Nat) : k≤2^k := by
  induction k with
  | zero => decide
  | succ k ih => have h := Nat.two_pow_pos k; rw [Nat.pow_succ]; omega

theorem amplify_population (a : Affine) (h : Good a) (s : Cylinder a) (B : Nat)
    (hlive : 0<weight s.pop) :
    ∃ bits : List Bool, bits.length≤F B+1 ∧
      B≤weight (runBits (next a h) s bits).pop := by
  by_cases hc : s.pop.c=[]
  · have hp : s.pop.p≠[] := by intro he; simp [weight,hc,he] at hlive
    obtain ⟨w,hw⟩ := List.exists_mem_of_ne_nil _ hp
    have hdiv := ((s.valid.2 w).mp hw).2.2.2
    obtain ⟨e,he⟩ := bit_exists a s.n s.b w h hdiv
    have hw' : w∈(next a h s e).pop.c := by
      simp only [next,step,List.mem_filter,List.mem_append,he,and_true]
      exact Or.inr hw
    obtain ⟨bits,hlen,hm⟩ := amplify_completed a h (next a h s e) w hw' B
    refine ⟨e::bits,by simp; omega,?_⟩
    change B≤weight (runBits (next a h) (next a h s e) bits).pop
    unfold weight
    have hh := pow_ge_self B
    omega
  · obtain ⟨w,hw⟩ := List.exists_mem_of_ne_nil _ hc
    obtain ⟨bits,hlen,hm⟩ := amplify_completed a h s w hw B
    refine ⟨bits,by omega,?_⟩
    unfold weight
    have hh := pow_ge_self B
    omega

#print axioms step_valid
#print axioms step_supermean
#print axioms amplify_population
end BB6.Agent21Dyadic
