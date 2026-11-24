import Q0HalfCoverage

namespace BB429Q0Macro.HalfStep
open BB429Q0Macro
set_option maxHeartbeats 8000000

/-- Symmetric windows of arbitrary length, crossing rank a*4^k+b. -/
def CrossWindow (a b k N : Nat) : Prop :=
  ∃ (s : Bool) (w v : List Bool) (p y Y P2 Y2 : Nat),
  w.length=N ∧ v.length=N ∧ 0<y ∧ 3*y<p ∧ valid s p ∧
  Trace s w p y (a*4^k+b) Y ∧ Trace (phase s w) v (a*4^k+b) Y P2 Y2

theorem trace_window {s w p y P Y a k N} (h : Trace s w p y P Y)
    (hy : 0<y) (hc : 3*y<p) (hv : valid s p)
    (hl : p+9*N≤a*4^k) (hh : a*4^k+8+9*N≤P) : ∃ b, b<9 ∧ CrossWindow a b k N := by
  obtain ⟨i,q,e,hi,hq,hq',hpre,hpost⟩ := rank_cross h (a*4^k) (by omega) (by omega)
  have hlen : (w.take i).length=i := by simp [Nat.min_eq_left hi]
  have hlen2 : (w.drop i).length=w.length-i := by simp
  have hr1 := trace_rank hpre
  have hr2 := trace_rank hpost
  have hk : N≤i := by omega
  have hk2 : N≤w.length-i := by omega
  obtain ⟨r,t,hpre1,hpre2⟩ := trace_split hpre (i-N)
  obtain ⟨q2,e2,hpost1,hpost2⟩ := trace_split hpost N
  obtain ⟨hs,hstrict⟩ := trace_strict hpre1 hy hc
  have hvalid := trace_valid hpre1 hv
  let b := q-a*4^k
  have hb' : b<9 := by dsimp [b]; omega
  have hqeq : q=a*4^k+b := by dsimp [b]; omega
  refine ⟨b,hb',phase s ((w.take i).take (i-N)),(w.take i).drop (i-N),(w.drop i).take N,
    r,t,e,q2,e2,?_,?_,hs,hstrict,hvalid,?_,?_⟩
  · simp [hlen]; omega
  · simp [hlen2,Nat.min_eq_left (show N≤w.length-i by omega)]
  · rwa [←hqeq]
  · have hphase : phase (phase s ((w.take i).take (i-N))) ((w.take i).drop (i-N))=phase s (w.take i) := by
      rw [←phase_append,List.take_append_drop]
    rwa [hphase,←hqeq]

private theorem pow_square (t : Nat) : 4^t=2^t*2^t := by
  rw [←Nat.pow_mul 2 2 t,show 2*t=t+t by omega,Nat.pow_add]

private theorem power_linear (t : Nat) (ht : 12≤t) : 256*(t+1)≤2^t := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases h : 12≤t
    · have hb := ih h
      rw [Nat.pow_succ]; omega
    · have he : t=11 := by omega
      subst t; decide

/-- An exponential window at an adjacent power of two fits in the rank span
    once the excess growth over doubling is at least 28*2^(t+1)+8. -/
theorem long_rank_cover (t p P : Nat) (ht : 12≤t) (hl : 4^t≤p) (hh : p<4^(t+1))
    (hP : 2*p+28*2^(t+1)+8≤P) :
    ∃ a k, (a=1 ∨ a=2) ∧ 12≤k ∧ p+9*2^k≤a*4^k ∧ a*4^k+8+9*2^k≤P := by
  have hpow : 4^(t+1)=4*4^t := by rw [Nat.pow_succ]; omega
  have hpow2 : 2^(t+1)=2*2^t := by rw [Nat.pow_succ]; omega
  have hlin := power_linear t ht
  have hquad := pow_square t
  have hq : 9*2^(t+1)≤4^(t+1) := by
    have h := Nat.mul_le_mul_left (2^t) (show 9≤2^t by omega)
    grind
  by_cases h₁ : p+9*2^t≤2*4^t
  · exact ⟨2,t,Or.inr rfl,ht,h₁,by omega⟩
  by_cases h₂ : p+9*2^(t+1)≤4^(t+1)
  · exact ⟨1,t+1,Or.inl rfl,by omega,by simpa using h₂,by simp; omega⟩
  · exact ⟨2,t+1,Or.inr rfl,by omega,by omega,by omega⟩

/-- Every large q0 path must have at least 2^k half-steps on each side
    of a power-of-two crossing at scale k. No empirical barrier assumption. -/
theorem q0_long_cross (u : Nat) (hu : 1000000≤u) (h : Path (8*u+5) (24*u+22) (6*u+4)) :
    ∃ a k b, (a=1 ∨ a=2) ∧ 12≤k ∧ b<9 ∧ CrossWindow a b k (2^k) := by
  obtain ⟨w,P,Y,hw,htrace⟩ := RankBarrier.trace_of_path h
  obtain ⟨t,hl,hh⟩ := scale_exists (2*(24*u+22)) (by omega)
  have ht : 12≤t := by
    by_cases he : t<12
    · have hpow := Nat.pow_le_pow_right (n:=4) (by decide) (show t+1≤12 by omega)
      have hval : 4^12=16777216 := by decide
      omega
    · omega
  have hlin := power_linear t ht
  have hquad := pow_square t
  have hpow2 : 2^(t+1)=2*2^t := by rw [Nat.pow_succ]; omega
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
  have hj : (14*2^(t+1)+11)*(t+1)≤w.length := by
    let J := 14*2^(t+1)+11
    have hbound := Nat.mul_le_mul_right (2^t) hlin
    have hsmall : 6*J+14≤256*2^t := by dsimp [J]; omega
    have hmul := Nat.mul_le_mul_right (t+1) hsmall
    have hmul' : 6*(J*(t+1))+14*(t+1)≤256*(t+1)*2^t := by
      rw [Nat.add_mul,Nat.mul_assoc] at hmul
      simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hmul
    have hj' : 6*(J*(t+1))+14≤4^t := by omega
    change J*(t+1)≤w.length
    rw [hw]
    omega
  have hextra := RankBarrier.extra_growth (k:=t+1) (j:=14*2^(t+1)+11) (by omega) htrace (by omega) (by omega) hP hj
  have hg : 2*(2*(24*u+22))+28*2^(t+1)+8≤2*P := by omega
  obtain ⟨a,k,ha,hk,h₁,h₂⟩ := long_rank_cover t _ (2*P) ht hl hh hg
  obtain ⟨b,hb,hcross⟩ := trace_window (expand_trace htrace) (by omega) (by omega) (by simp [valid,bit]) h₁ h₂
  exact ⟨a,k,b,ha,hk,hb,hcross⟩

theorem q0_of_no_long_cross {Reach : Nat→Nat→Prop} (src : Source Reach)
    (hbar : ∀ a k b, (a=1 ∨ a=2) → 12≤k → b<9 → ¬ CrossWindow a b k (2^k))
    {u n x y : Nat} (hu : 1000000≤u) (hn : n=23+32*u)
    (hx : x+24*u+19=13*2^n) (hy : y+13=2*x) : ¬ Reach x y := by
  intro hr
  obtain ⟨a,k,b,ha,hk,hb,hc⟩ := q0_long_cross u hu (q0_path src u n x y hn hx hy hr)
  exact hbar a k b ha hk hb hc

#print axioms q0_long_cross
#print axioms q0_of_no_long_cross
end BB429Q0Macro.HalfStep
