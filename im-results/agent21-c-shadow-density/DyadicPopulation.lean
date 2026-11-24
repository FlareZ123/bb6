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

theorem rnum_bit (a : Affine) (n : Nat) (b : Int) (w : List Nat) (h : Admissible a) :
    rnum a w (shiftBit n b true)=rnum a w b+P n*slope a w.reverse := by
  unfold rnum shiftBit
  simp only [if_true]
  rw [numer_affine_even _ _ _ h.1,numer_affine_even _ _ _ h.1,Int.mul_add,Int.mul_comm (slope a w.reverse) (P n)]
  omega

theorem rword_nonempty (w : List Nat) (hp : rpos w) (hn : w≠[]) :
    ∃ r v, w.reverse=r::v ∧ 0<r := by
  cases he : w.reverse with
  | nil => exact False.elim (hn (by simpa using he))
  | cons r v =>
    refine ⟨r,v,rfl,?_⟩
    unfold rpos at hp
    rw [he] at hp
    exact hp r (by simp)

theorem bit_unique (a : Affine) (n : Nat) (b : Int) (w : List Nat) (h : Admissible a)
    (hp : rpos w) (hn : w≠[]) :
    ¬(passes a (n+1) (shiftBit n b false) w=true ∧ passes a (n+1) (shiftBit n b true) w=true) := by
  intro ⟨h0,h1⟩
  rw [passes_iff] at h0 h1
  simp [shiftBit] at h0
  rw [rnum_bit _ _ _ _ h] at h1
  have hd := Int.dvd_sub h1 h0
  rw [show rnum a w b+P n*slope a w.reverse-rnum a w b=P n*slope a w.reverse by omega,P_add] at hd
  have he := (Int.mul_dvd_mul_iff_left (P_ne n)).mp hd
  have ho := slope_odd_nonempty a w.reverse h (rword_nonempty w hp hn)
  change 2∣slope a w.reverse at he
  have hm := Int.emod_eq_zero_of_dvd he
  omega

theorem bit_down (a : Affine) (n : Nat) (b : Int) (e : Bool) (w : List Nat) (h : Admissible a)
    (hp : P n∣rnum a w (shiftBit n b e)) : P n∣rnum a w b := by
  cases e
  · simpa [shiftBit] using hp
  · rw [rnum_bit _ _ _ _ h] at hp
    have hd := Int.dvd_sub hp (Int.dvd_mul_right (P n) (slope a w.reverse))
    simpa using hd

theorem bit_exists (a : Affine) (n : Nat) (b : Int) (w : List Nat) (h : Admissible a)
    (hpos : rpos w) (hn : w≠[]) (hp : P n∣rnum a w b) : ∃ e : Bool, passes a (n+1) (shiftBit n b e) w=true := by
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
    have ho := slope_odd_nonempty a w.reverse h (rword_nonempty w hpos hn)
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

theorem step_valid (a : Affine) (n : Nat) (b : Int) (Q : Pop) (e : Bool) (h : Admissible a)
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
    (h : ∀ x∈l, ¬(p x=true ∧ q x=true)) :
    (l.filter p).length+(l.filter q).length≤l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx := h x (by simp)
    have hi := ih (fun y hy=>h y (by simp [hy]))
    cases hp : p x <;> cases hq : q x <;> simp [List.filter_cons,hp,hq] at * <;> omega

theorem step_supermean (a : Affine) (n : Nat) (b : Int) (Q : Pop) (h : Admissible a) (hv : ValidPop a n b Q) :
    weight (step a n b Q false)+weight (step a n b Q true)≤2*weight Q := by
  let L := Q.c.map (1::·)++Q.p
  let R := Q.c.map (2::·)++Q.c.filterMap extendLast
  let p := passes a (n+1) (shiftBit n b false)
  let q := passes a (n+1) (shiftBit n b true)
  have hL := filters_le p q L (by
    intro w hw
    apply bit_unique a n b w h
    · simp only [L,List.mem_append,List.mem_map] at hw
      rcases hw with ⟨v,hv',rfl⟩|hw
      · exact (rpos_cons _ _).mpr ⟨by decide,((hv.1 v).mp hv').1⟩
      · exact ((hv.2 w).mp hw).2.1
    · simp only [L,List.mem_append,List.mem_map] at hw
      rcases hw with ⟨v,hv',rfl⟩|hw
      · simp
      · obtain ⟨r,v,rfl,_⟩ := ((hv.2 w).mp hw).1
        simp)
  have hR := filters_le p q R (by
    intro w hw
    apply bit_unique a n b w h
    · simp only [R,List.mem_append,List.mem_map,List.mem_filterMap] at hw
      rcases hw with ⟨v,hv',rfl⟩|⟨v,hv',he⟩
      · exact (rpos_cons _ _).mpr ⟨by decide,((hv.1 v).mp hv').1⟩
      · cases v with
        | nil => simp [extendLast] at he
        | cons r v =>
          simp [extendLast] at he
          subst w
          exact (rpos_cons _ _).mpr ⟨by omega,((rpos_cons _ _).mp ((hv.1 (r::v)).mp hv').1).2⟩
    · simp only [R,List.mem_append,List.mem_map,List.mem_filterMap] at hw
      rcases hw with ⟨v,hv',rfl⟩|⟨v,hv',he⟩
      · simp
      · cases v with
        | nil => simp [extendLast] at he
        | cons r v => simp [extendLast] at he; subst w; simp)
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
def next (a : Affine) (h : Admissible a) (s : Cylinder a) (e : Bool) : Cylinder a :=
  ⟨s.n+1,shiftBit s.n s.b e,step a s.n s.b s.pop e,step_valid a s.n s.b s.pop e h s.valid⟩

def runBits {α : Type} (next : α→Bool→α) (s : α) : List Bool→α
  | [] => s
  | e::w => runBits next (next s e) w

theorem runBits_append {α : Type} (f : α→Bool→α) (s : α) (u v : List Bool) :
    runBits f s (u++v)=runBits f (runBits f s u) v := by
  induction u generalizing s with
  | nil => rfl
  | cons e u ih => exact ih (f s e)

theorem chooseBits (a : Affine) (h : Admissible a) (s : Cylinder a) (n : Nat) (t : Int)
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

theorem amplify_completed (a : Affine) (h : Admissible a) (s : Cylinder a) (w : List Nat)
    (hw : w∈s.pop.c) (hne : w≠[]) (k : Nat) :
    ∃ bits : List Bool, bits.length≤F k ∧
      2^k≤(runBits (next a h) s bits).pop.c.length := by
  obtain ⟨hp,hc,hd⟩ := (s.valid.1 w).mp hw
  have hcomp : Compatible a w.reverse s.b := by unfold Compatible; change P (rcost w)∣rnum a w s.b; rwa [hc]
  let a1 := follow a w.reverse s.b
  have hg : Good a1 := by
    have hne' := rword_nonempty w hp hne
    obtain ⟨r,v,he,hr⟩ := hne'
    have hcost : 0<cost w.reverse := by rw [he,cost_cons]; omega
    refine ⟨?_,slope_odd_nonempty a w.reverse h ⟨r,v,he,hr⟩⟩
    change (a.sigma*P (cost w.reverse))%4=0
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : cost w.reverse≠0)
    rw [hk,show k.succ=k+1 by rfl,P_add]
    have hσ := h.1
    change (a.sigma*(P k*2))%4=0
    have heσ : a.sigma=2*(a.sigma/2) := by omega
    have hmul : a.sigma*(P k*2)=4*((a.sigma/2)*P k) := by
      calc
        a.sigma*(P k*2)=(2*(a.sigma/2))*(P k*2) := congrArg (fun t:Int=>t*(P k*2)) heσ
        _=(2*2)*((a.sigma/2)*P k) := by ac_rfl
        _=4*((a.sigma/2)*P k) := rfl
    rw [hmul]; omega
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
    · have hh := append_compatible_even a w.reverse v s.b W.b h.1 hcomp hvd
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

theorem amplify_population (a : Affine) (h : Admissible a) (s : Cylinder a) (B : Nat)
    (hlive : 0<weight s.pop) :
    ∃ bits : List Bool, bits.length≤F B+1 ∧
      B≤weight (runBits (next a h) s bits).pop := by
  by_cases hc : s.pop.c=[]
  · have hp : s.pop.p≠[] := by intro he; simp [weight,hc,he] at hlive
    obtain ⟨w,hw⟩ := List.exists_mem_of_ne_nil _ hp
    have hspec := (s.valid.2 w).mp hw
    have hne : w≠[] := by obtain ⟨r,v,rfl,_⟩ := hspec.1; simp
    obtain ⟨e,he⟩ := bit_exists a s.n s.b w h hspec.2.1 hne hspec.2.2.2
    have hw' : w∈(next a h s e).pop.c := by
      simp only [next,step,List.mem_filter,List.mem_append,he,and_true]
      exact Or.inr hw
    obtain ⟨bits,hlen,hm⟩ := amplify_completed a h (next a h s e) w hw' hne B
    refine ⟨e::bits,by simp; omega,?_⟩
    change B≤weight (runBits (next a h) (next a h s e) bits).pop
    unfold weight
    have hh := pow_ge_self B
    omega
  · obtain ⟨w,hw⟩ := List.exists_mem_of_ne_nil _ hc
    by_cases hne : w=[]
    · subst w
      have hn : s.n=0 := by have he := ((s.valid.1 []).mp hw).2.1; simpa [rcost,cost] using he.symm
      have hdiv : P s.n∣rnum a [1] s.b := by rw [hn]; simp [P]
      obtain ⟨e,he⟩ := bit_exists a s.n s.b [1] h (by simp [rpos,Positive]) (by simp) hdiv
      have hw' : [1]∈(next a h s e).pop.c := by
        simp only [next,step,List.mem_filter,List.mem_append,he,and_true,List.mem_map]
        exact Or.inl ⟨[],hw,rfl⟩
      obtain ⟨bits,hlen,hm⟩ := amplify_completed a h (next a h s e) [1] hw' (by simp) B
      refine ⟨e::bits,by simp; omega,?_⟩
      change B≤weight (runBits (next a h) (next a h s e) bits).pop
      unfold weight
      have hh := pow_ge_self B
      omega
    · obtain ⟨bits,hlen,hm⟩ := amplify_completed a h s w hw hne B
      refine ⟨bits,by omega,?_⟩
      unfold weight
      have hh := pow_ge_self B
      omega

#print axioms step_valid
#print axioms step_supermean
#print axioms amplify_population
end BB6.Agent21Dyadic
