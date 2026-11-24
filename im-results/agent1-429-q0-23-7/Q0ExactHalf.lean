import Q0WideWindow

namespace BB429Q0Macro.HalfStep
open BB429Q0Macro
set_option maxHeartbeats 8000000

/-- Exact phase lattice, including height parity at macro boundaries. -/
def lattice (s : Bool) (p y : Nat) : Prop := valid s p ∧ (s=false → y%2=0)

inductive ExactTrace : Bool → List Bool → Nat → Nat → Nat → Nat → Prop where
  | nil (s : Bool) (p y : Nat) (hl : lattice s p y) : ExactTrace s [] p y p y
  | cons (s d : Bool) {w : List Bool} {p y P Y : Nat}
      (hl : lattice s p y) (hd : numerator s d p y%4=0)
      (tail : ExactTrace (!s) w (p+len s d) (numerator s d p y/4) P Y) :
      ExactTrace s (d::w) p y P Y

theorem ExactTrace.trace {s w p y P Y} (h : ExactTrace s w p y P Y) : Trace s w p y P Y := by
  induction h with
  | nil => exact Trace.nil ..
  | cons s d hl hd ht ih => exact Trace.cons s d hd ih

theorem ExactTrace.initial {s w p y P Y} (h : ExactTrace s w p y P Y) : lattice s p y := by
  cases h <;> assumption

theorem ExactTrace.terminal {s w p y P Y} (h : ExactTrace s w p y P Y) : lattice (phase s w) P Y := by
  induction h with
  | nil => simpa [phase] using ‹lattice _ _ _›
  | cons s d hl hd ht ih => rw [phase_cons]; exact ih

theorem ExactTrace.append {s w v p y Q F P Y} (h : ExactTrace s w p y Q F)
    (t : ExactTrace (phase s w) v Q F P Y) : ExactTrace s (w++v) p y P Y := by
  induction h with
  | nil => simpa [phase] using t
  | cons s d hl hd ht ih =>
    rw [phase_cons] at t
    exact ExactTrace.cons s d hl hd (ih t)

theorem ExactTrace.split {s w p y P Y} (h : ExactTrace s w p y P Y) (n : Nat) :
    ∃ Q F, ExactTrace s (w.take n) p y Q F ∧ ExactTrace (phase s (w.take n)) (w.drop n) Q F P Y := by
  induction n generalizing s w p y with
  | zero => exact ⟨p,y,by simpa using ExactTrace.nil s p y h.initial,by simpa [phase] using h⟩
  | succ n ih =>
    cases h with
    | nil s _ _ hl => exact ⟨_,_,by simpa using ExactTrace.nil s _ _ hl,by simpa [phase] using ExactTrace.nil s _ _ hl⟩
    | @cons s d w p y P Y hl hd ht =>
      obtain ⟨Q,F,h₁,h₂⟩ := ih ht
      exact ⟨Q,F,ExactTrace.cons s d hl hd h₁,by simpa only [List.take_succ_cons,List.drop_succ_cons,phase_cons] using h₂⟩

/-- The two original half-steps satisfy the full lattice conditions. -/
theorem pair_exact (d : Digit) (p y : Nat) (hd : num d p y%16=0) :
    ExactTrace false [low d,high d] (2*p) (2*y) (2*nextP d p) (2*nextY d p y) := by
  have hd : 4 ∣ numerator false (low d) (2*p) (2*y) := by
    cases d <;> simp [num,BB429Q0Macro.digit,cost,offset,numerator,bit,off,low] at * <;> omega
  have h₁ : numerator false (low d) (2*p) (2*y)%4=0 := Nat.mod_eq_zero_of_dvd hd
  refine ExactTrace.cons false (low d) (by simp [lattice,valid,bit]) h₁ ?_
  have h₂ : numerator true (high d) (2*p+len false (low d)) (numerator false (low d) (2*p) (2*y)/4)%4=0 := by
    cases d <;> simp [num,BB429Q0Macro.digit,cost,offset,numerator,bit,off,len,low,high] at * <;> omega
  refine ExactTrace.cons true (high d) ?_ h₂ ?_
  · simp [lattice,valid,bit]
    cases d <;> simp [len,low] <;> omega
  have hp : 2*p+len false (low d)+len true (high d)=2*nextP d p := by
    cases d <;> simp [nextP,cost,len,low,high] <;> omega
  have hy : numerator true (high d) (2*p+len false (low d)) (numerator false (low d) (2*p) (2*y)/4)/4=2*nextY d p y := by
    cases d <;> simp [num,BB429Q0Macro.digit,cost,offset,numerator,bit,off,len,low,high,nextY] at * <;> omega
  rw [hp,hy]
  exact ExactTrace.nil false _ _ (by simp [lattice,valid,bit])

theorem expand_exact {w p y P Y} (h : RankBarrier.Trace w p y P Y) :
    ExactTrace false (expand w) (2*p) (2*y) (2*P) (2*Y) := by
  induction h with
  | nil => exact ExactTrace.nil _ _ _ (by simp [lattice,valid,bit])
  | cons d hd ht ih =>
    apply ExactTrace.append (pair_exact d _ _ hd)
    simpa [phase] using ih

/-- Conversely an aligned pair in the phase lattice is an original macro. -/
theorem pair_converse {d e : Bool} {p y P Y : Nat}
    (h : ExactTrace false [d,e] (2*p) (2*y) (2*P) (2*Y)) :
    ∃ D : Digit, low D=d ∧ high D=e ∧ num D p y%16=0 ∧ P=nextP D p ∧ Y=nextY D p y := by
  have unroll {s : Bool} {u v : Nat} {a b : Bool} {Q Z : Nat}
      (h : ExactTrace s [a,b] u v Q Z) :
      numerator s a u v%4=0 ∧
      numerator (!s) b (u+len s a) (numerator s a u v/4)%4=0 ∧
      Q=u+len s a+len (!s) b ∧
      Z=numerator (!s) b (u+len s a) (numerator s a u v/4)/4 := by
    cases h with
    | cons _ _ _ h₁ ht =>
      cases ht with
      | cons _ _ _ h₂ ht =>
        cases ht
        exact ⟨h₁,h₂,rfl,rfl⟩
  obtain ⟨h₁,h₂,hP,hY⟩ := unroll h
  cases d <;> cases e
  · exact ⟨.zero,rfl,rfl,by simp [num,BB429Q0Macro.digit,offset,numerator,bit,len,off] at *; omega,by simp [nextP,cost,len] at *; omega,by simp [nextY,num,BB429Q0Macro.digit,offset,numerator,bit,len,off] at *; omega⟩
  · exact ⟨.four,rfl,rfl,by simp [num,BB429Q0Macro.digit,offset,numerator,bit,len,off] at *; omega,by simp [nextP,cost,len] at *; omega,by simp [nextY,num,BB429Q0Macro.digit,offset,numerator,bit,len,off] at *; omega⟩
  · exact ⟨.one,rfl,rfl,by simp [num,BB429Q0Macro.digit,offset,numerator,bit,len,off] at *; omega,by simp [nextP,cost,len] at *; omega,by simp [nextY,num,BB429Q0Macro.digit,offset,numerator,bit,len,off] at *; omega⟩
  · exact ⟨.five,rfl,rfl,by simp [num,BB429Q0Macro.digit,offset,numerator,bit,len,off] at *; omega,by simp [nextP,cost,len] at *; omega,by simp [nextY,num,BB429Q0Macro.digit,offset,numerator,bit,len,off] at *; omega⟩

/-- A target in the strict cone has at most one predecessor and incoming bit.
    This holds even before imposing height parity. -/
theorem predecessor_unique (s d e : Bool) (p y q z P Y : Nat)
    (hp : 0<y ∧ 3*y<p) (hq : 0<z ∧ 3*z<q)
    (hP : P=p+len s d) (hQ : P=q+len s e)
    (hY : 4*Y=numerator s d p y) (hZ : 4*Y=numerator s e q z) :
    d=e ∧ p=q ∧ y=z := by
  cases s <;> cases d <;> cases e <;> simp [len,numerator,bit,off] at * <;> omega

/-- An exact crossing retains the lattice of every intermediate phase. -/
def ExactCrossWindow (a b k N : Nat) : Prop :=
  ∃ (s : Bool) (w v : List Bool) (p y Y P2 Y2 : Nat),
  w.length=N ∧ v.length=N ∧ 0<y ∧ 3*y<p ∧
  ExactTrace s w p y (a*4^k+b) Y ∧ ExactTrace (phase s w) v (a*4^k+b) Y P2 Y2

theorem exact_rank_cross {s w p y P Y} (h : ExactTrace s w p y P Y) (B : Nat)
    (hlo : p≤B) (hhi : B≤P) :
    ∃ i q e, i≤w.length ∧ B≤q ∧ q<B+9 ∧
      ExactTrace s (w.take i) p y q e ∧ ExactTrace (phase s (w.take i)) (w.drop i) q e P Y := by
  induction h with
  | nil s p y hl => exact ⟨0,p,y,by simp,by omega,by omega,by simpa using ExactTrace.nil s p y hl,by simpa [phase] using ExactTrace.nil s p y hl⟩
  | @cons s d w p y P Y hl hd ht ih =>
    by_cases he : p=B
    · exact ⟨0,p,y,by simp,by omega,by omega,by simpa using ExactTrace.nil s p y hl,by simpa [phase] using ExactTrace.cons s d hl hd ht⟩
    by_cases hn : p+len s d≤B
    · obtain ⟨i,q,e,hi,hq,hq',h1,h2⟩ := ih hn hhi
      exact ⟨i+1,q,e,by simp; omega,hq,hq',by simpa using ExactTrace.cons s d hl hd h1,by simpa only [List.take_succ_cons,List.drop_succ_cons,phase_cons] using h2⟩
    · have hc : len s d≤9 := by cases s <;> cases d <;> decide
      refine ⟨1,p+len s d,numerator s d p y/4,by simp,by omega,by omega,?_,?_⟩
      · simpa using ExactTrace.cons s d hl hd (ExactTrace.nil (!s) _ _ ht.initial)
      · simpa [phase] using ht

theorem trace_exact_window {s w p y P Y a k N} (h : ExactTrace s w p y P Y)
    (hy : 0<y) (hc : 3*y<p)
    (hl : p+9*N≤a*4^k) (hh : a*4^k+8+9*N≤P) : ∃ b, b<9 ∧ ExactCrossWindow a b k N := by
  obtain ⟨i,q,e,hi,hq,hq',hpre,hpost⟩ := exact_rank_cross h (a*4^k) (by omega) (by omega)
  have hlen : (w.take i).length=i := by simp [Nat.min_eq_left hi]
  have hlen2 : (w.drop i).length=w.length-i := by simp
  have hr1 := trace_rank hpre.trace
  have hr2 := trace_rank hpost.trace
  have hk : N≤i := by omega
  have hk2 : N≤w.length-i := by omega
  obtain ⟨r,t,hpre1,hpre2⟩ := hpre.split (i-N)
  obtain ⟨q2,e2,hpost1,hpost2⟩ := hpost.split N
  obtain ⟨hs,hstrict⟩ := trace_strict hpre1.trace hy hc
  let b := q-a*4^k
  have hb' : b<9 := by dsimp [b]; omega
  have hqeq : q=a*4^k+b := by dsimp [b]; omega
  refine ⟨b,hb',phase s ((w.take i).take (i-N)),(w.take i).drop (i-N),(w.drop i).take N,
    r,t,e,q2,e2,?_,?_,hs,hstrict,?_,?_⟩
  · simp [hlen]; omega
  · simp [hlen2,Nat.min_eq_left (show N≤w.length-i by omega)]
  · rwa [←hqeq]
  · have hphase : phase (phase s ((w.take i).take (i-N))) ((w.take i).drop (i-N))=phase s (w.take i) := by
      rw [←phase_append,List.take_append_drop]
    rwa [hphase,←hqeq]

/-- Every large q0 candidate forces a two-sided window of radius
    floor(4^k/(128*(k+1))) near a power-of-two rank. -/
theorem q0_wide_exact_cross (u : Nat) (hu : 1000000≤u)
    (h : Path (8*u+5) (24*u+22) (6*u+4)) :
    ∃ a k b, (a=1 ∨ a=2) ∧ 12≤k ∧ b<9 ∧ ExactCrossWindow a b k (wideRadius k) := by
  obtain ⟨w,P,Y,hw,htrace⟩ := RankBarrier.trace_of_path h
  obtain ⟨t,hl,hh⟩ := scale_exists (2*(24*u+22)) (by omega)
  have ht : 12≤t := by
    by_cases he : t<12
    · have hpow := Nat.pow_le_pow_right (n:=4) (by decide) (show t+1≤12 by omega)
      have hval : 4^12=16777216 := by decide
      omega
    · omega
  have hR := RankBarrier.trace_rank htrace
  have hP : P≤16^(t+1) := by
    have hpow := Nat.pow_mul 4 2 (t+1)
    have hpow' : 16^(t+1)=4^(t+1)*4^(t+1) := by
      rw [←hpow,show 2*(t+1)=(t+1)+(t+1) by omega,Nat.pow_add]
    have hge : 2≤4^(t+1) := by
      have := Nat.pow_le_pow_right (n:=4) (by decide) (show 1≤t+1 by omega)
      simp at this; omega
    have hbig := Nat.mul_le_mul_left (4^(t+1)) hge
    rw [hpow']
    omega
  have grow : ∀ j : Nat, 6*j*(t+1)+14≤2*(24*u+22) →
      2*(2*(24*u+22))+2*j≤2*P+14 := by
    intro j hj
    have hmul : 6*j*(t+1)=6*(j*(t+1)) := by rw [Nat.mul_assoc]
    have hj' : j*(t+1)≤w.length := by rw [hw]; omega
    have hg := RankBarrier.extra_growth (k:=t+1) (j:=j) (by omega) htrace
      (by omega) (by omega) hP hj'
    omega
  obtain ⟨a,k,ha,hk,h₁,h₂⟩ := wide_rank_cover t _ (2*P) ht hl hh grow
  obtain ⟨b,hb,hcross⟩ := trace_exact_window (expand_exact htrace) (by omega) (by omega) h₁ h₂
  exact ⟨a,k,b,ha,hk,hb,hcross⟩

theorem q0_of_no_wide_exact_cross {Reach : Nat→Nat→Prop} (src : Source Reach)
    (hbar : ∀ a k b, (a=1 ∨ a=2) → 12≤k → b<9 → ¬ ExactCrossWindow a b k (wideRadius k))
    {u n x y : Nat} (hu : 1000000≤u) (hn : n=23+32*u)
    (hx : x+24*u+19=13*2^n) (hy : y+13=2*x) : ¬ Reach x y := by
  intro hr
  obtain ⟨a,k,b,ha,hk,hb,hc⟩ := q0_wide_exact_cross u hu (q0_path src u n x y hn hx hy hr)
  exact hbar a k b ha hk hb hc

#print axioms expand_exact
#print axioms pair_converse
#print axioms predecessor_unique
#print axioms q0_wide_exact_cross
#print axioms q0_of_no_wide_exact_cross
end BB429Q0Macro.HalfStep
