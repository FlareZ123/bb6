import Q0DelayStrip

namespace BB429Q0Macro.HalfStep
set_option maxHeartbeats 8000000

theorem trace_of_formula (s : Bool) (w : List Bool) (p y P Y : Nat)
    (hp : P=p+lengthCost s w)
    (hy : modulus w*Y=(y:Int)+digits w*P+error s w) : Trace s w p y P Y := by
  induction w generalizing s p y with
  | nil =>
    simp [lengthCost,modulus,digits,error] at hp hy
    have hy' : Y=y := by omega
    subst P; subst Y
    exact .nil s p y
  | cons d w ih =>
    rw [modulus_cons,digits,error,lengthCost] at hy
    simp only [lengthCost] at hp
    have hn : (numerator s d p y:Int)=4*(modulus w*Y-digits w*P-error (!s) w) := by
      simp only [numerator,Int.natCast_add,Int.natCast_mul]
      rw [Int.mul_assoc] at hy
      cases d <;> simp [bit,Int.add_mul,Int.mul_assoc,Int.natCast_add] at * <;> omega
    have hd : numerator s d p y%4=0 := by omega
    have hY : modulus w*Y=((numerator s d p y/4:Nat):Int)+digits w*P+error (!s) w := by omega
    exact .cons s d hd (ih (!s) _ _ (by omega) hY)

/-- A nonterminal A-state automatically has even height. Hence the only
    extra condition on an ordinary exact-division trace is terminal parity. -/
theorem exact_of_trace {s w p y P Y} (h : Trace s w p y P Y) (hp : valid s p)
    (hY : phase s w=false → Y%2=0) : ExactTrace s w p y P Y := by
  induction h with
  | nil s p y =>
    exact .nil s p y ⟨hp,by simpa [phase] using hY⟩
  | @cons s d w p y P Y hd ht ih =>
    have hl : lattice s p y := by
      refine ⟨hp,?_⟩
      intro hs
      subst s
      unfold valid at hp
      cases d <;> simp [numerator,bit,off] at hd hp <;> omega
    exact .cons s d hl hd (ih (valid_step s d _ hp) (by simpa only [phase_cons] using hY))

def seedRank (a : Nat) (s : Bool) (w : List Bool) (q : Int) : Int :=
  a*modulus w+q-lengthCost s w

def seedHeight (s : Bool) (w : List Bool) (q e : Int) : Int :=
  modulus w*e-q*digits w-error s w

/-- The initial strict cone can be tested directly from a carry and its
    k-bit history. No search over the large initial height is needed. -/
def seedOK (a : Nat) (s : Bool) (w : List Bool) (q e : Int) : Prop :=
  0<seedHeight s w q e ∧ 3*seedHeight s w q e<seedRank a s w q ∧
  seedRank a s w q%2=bit s ∧ 0≤(a:Int)*digits w+e

theorem DelayTrace.initial {a s w q e v W Q F} (h : DelayTrace a s w q e v W Q F) : stripOK a s w q e := by
  cases h <;> assumption

theorem seed_of_history {s w p y P Y} (h : ExactTrace s w p y P Y) (hy : 0<y) (hc : 3*y<p) (a : Nat) :
    seedOK a s w ((P:Int)-a*modulus w) ((Y:Int)-a*digits w) := by
  have hf := trace_formula h.trace
  have hp : seedRank a s w ((P:Int)-a*modulus w)=p := by unfold seedRank; omega
  have hY : seedHeight s w ((P:Int)-a*modulus w) ((Y:Int)-a*digits w)=y := by
    unfold seedHeight
    grind
  have hv := h.initial.1
  unfold valid at hv
  unfold seedOK
  rw [hp,hY]
  refine ⟨by omega,by omega,by omega,by omega⟩

theorem history_of_seed {a s w q e} (h : seedOK a s w q e)
    (ok : stripOK a (phase s w) w q e) :
    ∃ p y P Y : Nat, 0<y ∧ 3*y<p ∧ ExactTrace s w p y P Y ∧
      (P:Int)=a*modulus w+q ∧ (Y:Int)=a*digits w+e := by
  let p := (seedRank a s w q).toNat
  let y := (seedHeight s w q e).toNat
  let P := ((a:Int)*modulus w+q).toNat
  let Y := ((a:Int)*digits w+e).toNat
  have hp : (p:Int)=seedRank a s w q := Int.toNat_of_nonneg (by have := h.1; have := h.2.1; omega)
  have hy : (y:Int)=seedHeight s w q e := Int.toNat_of_nonneg (by have := h.1; omega)
  have hP : (P:Int)=a*modulus w+q := Int.toNat_of_nonneg (by have := h.1; have := h.2.1; unfold seedRank at *; omega)
  have hY : (Y:Int)=a*digits w+e := Int.toNat_of_nonneg h.2.2.2
  have hpr : P=p+lengthCost s w := by unfold seedRank at hp; omega
  have hyr : modulus w*Y=(y:Int)+digits w*P+error s w := by
    rw [hY,hy,hP]
    unfold seedHeight
    grind
  have ht := trace_of_formula s w p y P Y hpr hyr
  have hv : valid s p := by
    have hh := h.2.2.1
    unfold valid
    omega
  have hpar : phase s w=false → Y%2=0 := by
    intro hs
    have hh := ok.2.2.1 hs
    omega
  exact ⟨p,y,P,Y,by have := h.1; omega,by have := h.2.1; omega,exact_of_trace ht hv hpar,hP,hY⟩

/-- Exact delayed-carry criterion for a symmetric window. The first k bits
    are the seed history, and the next N-k bits lead to the central rank. -/
def StripCross (a b k N : Nat) : Prop :=
  ∃ (s : Bool) (w v z U W : List Bool) (q e E Q F : Int),
  w.length=k ∧ v.length=N-k ∧ z.length=N ∧ seedOK a s w q e ∧
  DelayTrace a (phase s w) w q e v U b E ∧
  DelayTrace a (phase (phase s w) v) U b E z W Q F

theorem DelayTrace.split {a s w q e v W Q F} (h : DelayTrace a s w q e v W Q F) (n : Nat) :
    ∃ U r f, DelayTrace a s w q e (v.take n) U r f ∧
      DelayTrace a (phase s (v.take n)) U r f (v.drop n) W Q F := by
  induction n generalizing s w q e v with
  | zero => exact ⟨w,q,e,by simpa using DelayTrace.nil s w q e h.initial,by simpa [phase] using h⟩
  | succ n ih =>
    cases h with
    | nil s w q e ok => exact ⟨_,_,_,by simpa using DelayTrace.nil s _ _ _ ok,by simpa [phase] using DelayTrace.nil s _ _ _ ok⟩
    | @cons s r d w v W q e E Q F ok he ht =>
      obtain ⟨U,R,G,h₁,h₂⟩ := ih ht
      exact ⟨U,R,G,.cons s r d ok he h₁,by simpa only [List.take_succ_cons,List.drop_succ_cons,phase_cons] using h₂⟩

theorem trace_functional {s w p y P Y Q Z} (h : Trace s w p y P Y) (h' : Trace s w p y Q Z) : P=Q ∧ Y=Z := by
  obtain ⟨hp,hy⟩ := trace_formula h
  obtain ⟨hq,hz⟩ := trace_formula h'
  have he : P=Q := by omega
  rw [he] at hy
  have hh : modulus w*(Y:Int)=modulus w*(Z:Int) := by omega
  have hne : modulus w≠0 := by have := modulus_pos w; omega
  have hYZ := Int.eq_of_mul_eq_mul_left hne hh
  exact ⟨he,by omega⟩

theorem strip_cross_iff (a b k N : Nat) (hk : 0<k) (hN : k≤N) (hsize : 5*(b+9*N)≤2*4^k) :
    ExactCrossWindow a b k N ↔ StripCross a b k N := by
  constructor
  · rintro ⟨s,w,v,p,y,Y,P2,Y2,hw,hv,hy,hc,h₁,h₂⟩
    obtain ⟨p1,y1,hpre,hmid⟩ := h₁.split k
    have hl : (w.take k).length=k := by simp [hw,Nat.min_eq_left hN]
    have hl' : (w.drop k).length=N-k := by simp [hw]
    have hne : w.take k≠[] := by intro he; rw [he] at hl; simp at hl; omega
    have hM : modulus (w.take k)=(4:Int)^k := by simp [modulus,hl]
    have hpow : ((4^k:Nat):Int)=(4:Int)^k := by simp
    have hqcenter : ((a*4^k+b:Nat):Int)-a*modulus (w.take k)=b := by
      rw [hM,←hpow]; simp only [Int.natCast_add,Int.natCast_mul]; omega
    have hr := trace_rank h₂.trace
    have hsize' : 5*((P2:Int)-a*modulus (w.take k))≤2*modulus (w.take k) := by
      rw [hM,←hpow]
      have hsizeI : (5*(b+9*N):Int)≤2*(4^k:Nat) := by omega
      simp only [hv] at hr
      have hrI : (P2:Int)≤(a:Int)*(4^k:Nat)+b+9*N := by exact_mod_cast hr.2
      omega
    have hph : phase (phase s (w.take k)) (w.drop k)=phase s w := by rw [←phase_append,List.take_append_drop]
    rw [←hph] at h₂
    have hall := hmid.append h₂
    obtain ⟨W,hdelay,hW⟩ := delay_of_exact hall a hpre rfl hne hy hc hsize'
    obtain ⟨U,r,f,hfront,hback⟩ := hdelay.split (N-k)
    have htake : ((w.drop k)++v).take (N-k)=w.drop k := by rw [←hl']; simp
    have hdrop : ((w.drop k)++v).drop (N-k)=v := by rw [←hl']; simp
    rw [htake] at hfront hback
    rw [hdrop] at hback
    have hlenU := hfront.length_eq
    have hmodU : modulus U=modulus (w.take k) := by simp [modulus,hlenU]
    obtain ⟨P',Y',htr,hP',hY'⟩ := exact_of_delay hfront p1 y1 (by omega) (by omega)
    have hP'':P'=a*4^k+b := (trace_functional htr.trace hmid.trace).1
    have heq : r=(b:Int) := by rw [hP'',hmodU] at hP'; omega
    rw [heq] at hfront hback
    exact ⟨s,w.take k,w.drop k,v,U,W,_,_,f,_,_,hl,hl',hv,seed_of_history hpre hy hc a,hfront,hback⟩
  · rintro ⟨s,w,v,z,U,W,q,e,E,Q,F,hw,hv,hz,hseed,h₁,h₂⟩
    obtain ⟨p,y,p1,y1,hy,hc,hpre,hp1,hy1⟩ := history_of_seed hseed h₁.initial
    obtain ⟨P,Y,hfront,hP,hY⟩ := exact_of_delay h₁ p1 y1 hp1 hy1
    have hlenU := h₁.length_eq
    have hMU : modulus U=(4:Int)^k := by simp [modulus,hlenU,hw]
    have heq : P=a*4^k+b := by
      rw [hMU] at hP
      have hh : ((a*4^k+b:Nat):Int)=(a:Int)*(4:Int)^k+b := by simp
      omega
    obtain ⟨P2,Y2,hback,hP2,hY2⟩ := exact_of_delay h₂ P Y hP hY
    have hph : phase s (w++v)=phase (phase s w) v := phase_append s w v
    unfold ExactCrossWindow
    rw [←heq]
    refine ⟨s,w++v,z,p,y,Y,P2,Y2,?_,hz,hy,hc,hpre.append hfront,?_⟩
    · simp [hw,hv]; omega
    · rw [hph]; exact hback

theorem wide_strip_size (k b : Nat) (hk : 12≤k) (hb : b<9) :
    k≤wideRadius k ∧ 5*(b+9*wideRadius k)≤2*4^k := by
  have hN := wideRadius_ge_sqrt k hk
  have hpow : ∀ n : Nat, n+1≤2^n := by
    intro n
    induction n with
    | zero => decide
    | succ n ih => rw [Nat.pow_succ]; omega
  have hsmall := hpow k
  have hdiv := Nat.div_mul_le_self (4^k) (128*(k+1))
  have hdiv' : wideRadius k*(128*(k+1))≤4^k := hdiv
  have hN0 : 128*wideRadius k≤4^k := by
    have hh := Nat.mul_le_mul_left (wideRadius k) (show 128≤128*(k+1) by omega)
    rw [Nat.mul_comm (wideRadius k) 128] at hh
    omega
  have hbig : 4096≤2^k := Nat.le_trans (by decide : 4096≤2^12) (Nat.pow_le_pow_right (by decide) hk)
  omega

/-- The complete remaining near-power obstruction is an exact signed
    delayed-bit window. Its rank/height carries need not be nonnegative. -/
theorem q0_wide_strip_cross (u : Nat) (hu : 1000000≤u)
    (h : BB429Q0Macro.Path (8*u+5) (24*u+22) (6*u+4)) :
    ∃ a k b, (a=1 ∨ a=2) ∧ 12≤k ∧ b<9 ∧ StripCross a b k (wideRadius k) := by
  obtain ⟨a,k,b,ha,hk,hb,hcross⟩ := q0_wide_exact_cross u hu h
  have hs := wide_strip_size k b hk hb
  exact ⟨a,k,b,ha,hk,hb,(strip_cross_iff a b k (wideRadius k) (by omega) hs.1 hs.2).mp hcross⟩

theorem q0_of_no_wide_strip {Reach : Nat→Nat→Prop} (src : BB429Q0Macro.Source Reach)
    (hbar : ∀ a k b, (a=1 ∨ a=2) → 12≤k → b<9 → ¬ StripCross a b k (wideRadius k))
    {u n x y : Nat} (hu : 1000000≤u) (hn : n=23+32*u)
    (hx : x+24*u+19=13*2^n) (hy : y+13=2*x) : ¬ Reach x y := by
  intro hr
  obtain ⟨a,k,b,ha,hk,hb,hcross⟩ := q0_wide_strip_cross u hu (BB429Q0Macro.q0_path src u n x y hn hx hy hr)
  exact hbar a k b ha hk hb hcross

#print axioms trace_of_formula
#print axioms exact_of_trace
#print axioms seed_of_history
#print axioms history_of_seed
#print axioms strip_cross_iff
#print axioms q0_of_no_wide_strip
end BB429Q0Macro.HalfStep
