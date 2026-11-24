import BlockIntervalLow

namespace CascadePeriodic

inductive ResetPath : Nat → Nat → Nat → Prop where
  | nil (h : Nat) : ResetPath 0 h h
  | cons {n h u v : Nat} : Grammar h u → ResetPath n u v → ResetPath (n+1) h v

theorem ResetPath.append {n m h u v : Nat} (p : ResetPath n h u)
    (q : ResetPath m u v) : ResetPath (n+m) h v := by
  induction p with
  | nil h => simpa using q
  | @cons n h u w he hp ih =>
    rw [show n+1+m=n+m+1 by omega]
    exact .cons he (ih q)

/-- Absolute linear offset t; relative exponential coefficient s. -/
structure Summary where
  a : Nat
  d : Nat
  r : Nat
  s : Nat
  t : Nat
  steps : Nat
  deriving Repr

def Summary.one : Summary := ⟨0,0,1,0,0,0⟩
def Summary.token (k a δ : Nat) : Summary :=
  ⟨a+1,δ,3^a,16*3^a,(2*k+5)*3^a,1⟩
def Summary.merge (l r : Summary) : Summary :=
  ⟨l.a+r.a,l.d+r.d,l.r*r.r,r.r*l.s+2^(l.a+l.d)*r.s,
    r.r*l.t+2^l.a*r.t,l.steps+r.steps⟩

def AffineRel (q : Summary) (h k u k' : Nat) : Prop :=
  k'=k+q.d ∧ 2^q.a*(2*u+5)=q.r*(2*h+5)+q.s*2^k+q.t

theorem affine_one (h k : Nat) : AffineRel Summary.one h k h k := by simp [AffineRel,Summary.one]

theorem affine_token (h u k a δ : Nat) (hu : Unified h u k a) :
    AffineRel (Summary.token k a δ) h k u (k+δ) := by
  refine ⟨rfl,?_⟩
  dsimp [Summary.token]
  have he := hu.2
  grind

theorem affine_merge (l r : Summary) (h k u k' v k'' : Nat)
    (hl : AffineRel l h k u k') (hr : AffineRel r u k' v k'') :
    AffineRel (l.merge r) h k v k'' := by
  obtain ⟨hk,he⟩ := hl
  obtain ⟨hk',he'⟩ := hr
  subst k'
  refine ⟨by simp [Summary.merge]; omega,?_⟩
  dsimp [Summary.merge]
  rw [Nat.pow_add 2 l.a r.a,Nat.pow_add 2 l.a l.d]
  rw [Nat.pow_add 2 k l.d] at he'
  grind

/-- The single congruence argument relies on these elementary word-summary
    parity properties. A zero-denominator-exponent summary is the empty word. -/
def Shape (q : Summary) : Prop :=
  q.r%2=1 ∧ q.s%2=0 ∧ (q.a=0 → q=Summary.one) ∧ (0<q.a → q.t%2=1)

private theorem odd_three (a : Nat) : 3^a%2=1 := by
  induction a with
  | zero => decide
  | succ a ih => rw [Nat.pow_succ,Nat.mul_mod,ih]

private theorem even_pow (a : Nat) (ha : 0<a) : 2^a%2=0 := by
  cases a with
  | zero => omega
  | succ n => rw [Nat.pow_succ]; simp

theorem shape_one : Shape Summary.one := by simp [Shape,Summary.one]

theorem shape_token (k a δ : Nat) : Shape (Summary.token k a δ) := by
  unfold Shape Summary.token
  dsimp
  refine ⟨odd_three a,?_,by omega,?_⟩
  · rw [Nat.mul_mod]
    simp
  · intro _
    rw [Nat.mul_mod,odd_three]
    omega

theorem shape_merge (l r : Summary) (hl : Shape l) (hr : Shape r) : Shape (l.merge r) := by
  obtain ⟨hlr,hls,hlz,hlt⟩ := hl
  obtain ⟨hrr,hrs,hrz,hrt⟩ := hr
  unfold Shape Summary.merge
  dsimp
  refine ⟨?_,?_,?_,?_⟩
  · rw [Nat.mul_mod,hlr,hrr]
  · rw [Nat.add_mod,Nat.mul_mod r.r l.s,Nat.mul_mod (2^(l.a+l.d)) r.s,hls,hrs]
    simp
  · intro h
    have h1 := hlz (by omega)
    have h2 := hrz (by omega)
    rw [h1,h2]
    rfl
  · intro h
    by_cases ha : l.a=0
    · have h1 := hlz ha
      have h2 := hrt (by omega)
      rw [h1]
      simp [Summary.one,h2]
    · rw [Nat.add_mod,Nat.mul_mod r.r l.t,Nat.mul_mod (2^l.a) r.t,hrr,hlt (by omega),even_pow _ (by omega)]
      simp

/-- A final integral endpoint for a concatenated word implies an integral
    midpoint. The midpoint is also odd: the next nonempty word has an odd
    constant term, or the right word is empty and the midpoint is final. -/
theorem split_congruence (l r : Summary) (x y k : Nat)
    (hr : Shape r) (hy : y%2=1)
    (he : 2^(l.merge r).a*y=(l.merge r).r*x+(l.merge r).s*2^k+(l.merge r).t) :
    ∃m, m%2=1 ∧ 2^l.a*m=l.r*x+l.s*2^k+l.t ∧
      2^r.a*y=r.r*m+r.s*2^(k+l.d)+r.t := by
  obtain ⟨hrr,hrs,hrz,hrt⟩ := hr
  let N := l.r*x+l.s*2^k+l.t
  let T := r.s*2^(k+l.d)+r.t
  have hfull : 2^l.a*(2^r.a*y)=r.r*N+2^l.a*T := by
    dsimp [Summary.merge] at he
    rw [Nat.pow_add 2 l.a r.a,Nat.pow_add 2 l.a l.d] at he
    dsimp [N,T]
    rw [Nat.pow_add 2 k l.d]
    grind
  have hmod := congrArg (fun z : Nat => z%2^l.a) hfull
  change (2^l.a*(2^r.a*y))%2^l.a=(r.r*N+2^l.a*T)%2^l.a at hmod
  have hzero (v : Nat) : (2^l.a*v)%2^l.a=0 := Nat.mod_eq_zero_of_dvd ⟨v,rfl⟩
  rw [hzero,Nat.add_mod,hzero,Nat.add_zero,Nat.mod_mod] at hmod
  have hdiv := Nat.mod_add_div (r.r*N) (2^l.a)
  rw [←hmod,Nat.zero_add] at hdiv
  obtain ⟨m,hm,_⟩ := cancel_two_pow_odd l.a r.r ((r.r*N)/2^l.a) N hrr hdiv
  have hright : 2^r.a*y=r.r*m+T := by
    rw [hm] at hfull
    have hh : 2^l.a*(2^r.a*y)=2^l.a*(r.r*m+T) := by
      calc
        2^l.a*(2^r.a*y)=r.r*(2^l.a*m)+2^l.a*T := hfull
        _=2^l.a*(r.r*m+T) := by rw [Nat.mul_add (2^l.a) (r.r*m) T]; congr 1; ac_rfl
    exact Nat.mul_left_cancel (Nat.pow_pos (by decide)) hh
  have hodd : m%2=1 := by
    by_cases ha : r.a=0
    · have hr := hrz ha
      rw [hr] at hright
      simp [Summary.one,T,hr] at hright
      omega
    · have hpar := congrArg (fun z : Nat => z%2) hright
      change (2^r.a*y)%2=(r.r*m+T)%2 at hpar
      dsimp [T] at hpar
      rw [Nat.mul_mod (2^r.a),even_pow _ (by omega),Nat.add_mod (r.r*m),Nat.mul_mod r.r,hrr,
        Nat.add_mod (r.s*2^(k+l.d)),Nat.mul_mod r.s,hrs,hrt (by omega)] at hpar
      omega
  exact ⟨m,hodd,hm.symm,by simpa [T,Nat.add_assoc] using hright⟩

structure High where
  k : Nat
  lo : Nat
  hi : Nat
  deriving Repr

def highSafe (s : High) : Prop :=
  8*scale<s.lo+(correction s.k 3).1 ∧ s.hi+(correction s.k 5).2<16*scale
instance (s : High) : Decidable (highSafe s) := by unfold highSafe; infer_instance

def highAdvance (s : High) (a δ : Nat) : High :=
  let c := correction s.k 5
  let p := 2^(a+1+δ)
  ⟨s.k+δ,(floorCeil ((s.lo+16*scale+c.1)*3^a) p).1,
    (floorCeil ((s.hi+16*scale+c.2)*3^a) p).2⟩

inductive HighCert where
  | empty
  | atom (a δ : Nat)
  | branch (l r : HighCert)
  deriving Repr

def checkHigh (s : High) : HighCert → Option (High × Summary)
  | .empty => some (s,Summary.one)
  | .atom a δ => if highSafe s then some (highAdvance s a δ,Summary.token s.k a δ) else none
  | .branch l r => do
    let (t,p) ← checkHigh s l
    let (u,q) ← checkHigh t r
    pure (u,p.merge q)

theorem checkHigh_shape (c : HighCert) (s t : High) (q : Summary)
    (hc : checkHigh s c=some (t,q)) : Shape q := by
  induction c generalizing s t q with
  | empty =>
    simp [checkHigh] at hc
    obtain ⟨rfl,rfl⟩ := hc
    exact shape_one
  | atom a δ =>
    simp only [checkHigh] at hc
    split at hc
    · simp at hc
      obtain ⟨rfl,rfl⟩ := hc
      exact shape_token ..
    · simp at hc
  | branch l r ihl ihr =>
    simp only [checkHigh] at hc
    cases hl : checkHigh s l with
    | none => simp [hl] at hc
    | some z =>
      rcases z with ⟨v,p⟩
      simp [hl] at hc
      cases hr : checkHigh v r with
      | none => simp [hr] at hc
      | some z =>
        rcases z with ⟨w,q'⟩
        simp [hr] at hc
        obtain ⟨rfl,rfl⟩ := hc
        exact shape_merge _ _ (ihl s v p hl) (ihr v w q' hr)

private theorem three_odd' (a : Nat) : 3^a%2=1 := by
  induction a with
  | zero => decide
  | succ a ih => rw [Nat.pow_succ,Nat.mul_mod,ih]

/-- An integral odd result of the centered single-reset formula has the
    correct centered form, and the valid band makes it a true reset. -/
theorem realize_centered (h y k a : Nat) (hv : Valid h k) (hy : y%2=1)
    (he : 2^(a+1)*y=3^a*((2*h+5)+16*2^k+2*k+5)) :
    ∃u, y=2*u+5 ∧ Grammar h u := by
  obtain ⟨d,hd,hout⟩ := cancel_two_pow_odd (a+1) (3^a) y _ (three_odd' a) he
  have hdodd : d%2=1 := by
    rw [hout,Nat.mul_mod,three_odd'] at hy
    omega
  have hp : 1≤2^k := Nat.one_le_pow k 2 (by decide)
  have hpos : 1≤d := by omega
  have hyge : 5≤y := by
    rw [hout]
    by_cases ha : 2≤a
    · have h3 : 9≤3^a := Nat.pow_le_pow_right (n:=3) (by decide) ha
      exact Nat.le_trans (by omega : 5≤9*d) (Nat.mul_le_mul_right _ h3)
    · have hc : a=0 ∨ a=1 := by omega
      rcases hc with rfl|rfl <;> simp at hd ⊢ <;> omega
  let u := (y-5)/2
  have hu : y=2*u+5 := by dsimp [u]; omega
  refine ⟨u,hu,(grammar_iff_unified h u).2 ⟨k,a,hv,?_⟩⟩
  rw [←hu]
  exact he

/-- The high-only certificate plus ONE final exact congruence realizes all
    intermediate reset valuations, source bands and the actual reset path. -/
theorem checkHigh_sound (c : HighCert) (h y : Nat) (s t : High) (q : Summary)
    (hy : y%2=1) (hg : Encloses (2*h+5) s.k scale s.lo s.hi)
    (he : 2^q.a*y=q.r*(2*h+5)+q.s*2^s.k+q.t)
    (hc : checkHigh s c=some (t,q)) :
    ∃u, y=2*u+5 ∧ ResetPath q.steps h u ∧ t.k=s.k+q.d ∧ Encloses y t.k scale t.lo t.hi := by
  induction c generalizing h y s t q with
  | empty =>
    simp [checkHigh] at hc
    obtain ⟨rfl,rfl⟩ := hc
    have hh : y=2*h+5 := by simpa [Summary.one] using he
    refine ⟨h,hh,.nil h,by simp [Summary.one],?_⟩
    rwa [hh]
  | atom a δ =>
    simp only [checkHigh] at hc
    split at hc
    · rename_i hsafe
      simp at hc
      obtain ⟨rfl,rfl⟩ := hc
      have hv := interval_nonfatal_band h s.k scale s.lo s.hi _ _ hg
        (correction_sound s.k 3 (by decide)).1 (correction_sound s.k 5 (by decide)).2 hsafe.1 hsafe.2
      have he' : 2^(a+1)*y=3^a*((2*h+5)+16*2^s.k+2*s.k+5) := by
        dsimp [Summary.token] at he
        grind
      obtain ⟨u,hu,hgram⟩ := realize_centered h y s.k a hv hy he'
      refine ⟨u,hu,.cons hgram (.nil u),rfl,?_⟩
      exact interval_step _ _ _ _ _ _ _ _ _ _ _ _ hg (correction_sound s.k 5 (by decide)) he'
        (floorCeil_sound _ _ (Nat.pow_pos (by decide))).1 (floorCeil_sound _ _ (Nat.pow_pos (by decide))).2
    · simp at hc
  | branch l r ihl ihr =>
    simp only [checkHigh] at hc
    cases hl : checkHigh s l with
    | none => simp [hl] at hc
    | some z =>
      rcases z with ⟨v,p⟩
      simp [hl] at hc
      cases hr : checkHigh v r with
      | none => simp [hr] at hc
      | some z =>
        rcases z with ⟨w,q'⟩
        simp [hr] at hc
        obtain ⟨rfl,rfl⟩ := hc
        obtain ⟨m,hm,hleft,hright⟩ := split_congruence p q' (2*h+5) y s.k (checkHigh_shape r v w q' hr) hy he
        obtain ⟨u,hu,hpath,hk,hbounds⟩ := ihl h m s v p hm hg hleft hl
        rw [hu,←hk] at hright
        rw [hu] at hbounds
        obtain ⟨z,hz,hpath2,hk2,hbounds2⟩ := ihr u y v w q' hy hbounds hright hr
        refine ⟨z,hz,hpath.append hpath2,by simp [Summary.merge]; omega,hbounds2⟩

def initHigh (h k : Nat) : High :=
  let c := floorCeil ((2*h+5)*scale) (2^k)
  ⟨k,c.1,c.2⟩

def checkHighBlock (h k : Nat) (c : HighCert) : Option (Nat × Nat) := do
  let (_,q) ← checkHigh (initHigh h k) c
  let N := q.r*(2*h+5)+q.s*2^k+q.t
  if N%2^(q.a+1)=2^q.a then some (q.steps,(N/2^q.a-5)/2) else none

theorem checkHighBlock_sound (h k n u : Nat) (c : HighCert)
    (hc : checkHighBlock h k c=some (n,u)) : ResetPath n h u := by
  unfold checkHighBlock at hc
  cases he : checkHigh (initHigh h k) c with
  | none => simp [he] at hc
  | some z =>
    rcases z with ⟨t,q⟩
    simp [he] at hc
    obtain ⟨hmod,rfl,rfl⟩ := hc
    let N := q.r*(2*h+5)+q.s*2^k+q.t
    have hmod' : N%2^(q.a+1)=2^q.a := hmod
    have hlt : 2^q.a<2^(q.a+1) := Nat.pow_lt_pow_right (by decide) (by omega)
    obtain ⟨y,hy,hodd,_⟩ := valuation_from_low N (2^q.a) (q.a+1) q.a (by omega) hmod' (Nat.mod_eq_of_lt hlt)
    have hinit : Encloses (2*h+5) (initHigh h k).k scale (initHigh h k).lo (initHigh h k).hi :=
      floorCeil_sound _ _ (Nat.pow_pos (by decide))
    obtain ⟨v,hv,hpath,_,_⟩ := checkHigh_sound c h y (initHigh h k) t q hodd hinit (by simpa [initHigh,N] using hy.symm) he
    change ResetPath q.steps h ((N/2^q.a-5)/2)
    rw [hy,Nat.mul_div_cancel_left _ (Nat.pow_pos (by decide)),hv]
    simpa using hpath

#print axioms split_congruence
#print axioms checkHighBlock_sound
end CascadePeriodic
