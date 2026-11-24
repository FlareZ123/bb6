import Q0HalfStep
import Q0Growth

namespace BB429Q0Macro.HalfStep
open BB429Q0Macro
set_option maxHeartbeats 8000000

def Cross2 (a b k : Nat) : Prop :=
  ∃ (s : Bool) (w v z : List Bool) (p y Y P2 Y2 P3 Y3 : Nat),
  w.length=k ∧ v.length=k ∧ z.length=k ∧ 0<y ∧ 3*y<p ∧ valid s p ∧
  Trace s w p y (a*4^k+b) Y ∧
  Trace (phase s w) v (a*4^k+b) Y P2 Y2 ∧
  Trace (phase (phase s w) v) z P2 Y2 P3 Y3

theorem rank_cross {s w p y P Y} (h : Trace s w p y P Y) (B : Nat)
    (hlo : p≤B) (hhi : B≤P) :
    ∃ i q e, i≤w.length ∧ B≤q ∧ q<B+9 ∧
      Trace s (w.take i) p y q e ∧ Trace (phase s (w.take i)) (w.drop i) q e P Y := by
  induction h with
  | nil => exact ⟨0,_,_,by simp,by omega,by omega,by simp; exact .nil ..,by simp [phase]; exact .nil ..⟩
  | @cons s d w p y P Y hd ht ih =>
    by_cases he : p=B
    · exact ⟨0,p,y,by simp,by omega,by omega,by simp; exact .nil ..,by simpa [phase] using Trace.cons s d hd ht⟩
    by_cases hn : p+len s d≤B
    · obtain ⟨i,q,e,hi,hq,hq',h1,h2⟩ := ih hn hhi
      exact ⟨i+1,q,e,by simp; omega,hq,hq',by simpa using Trace.cons s d hd h1,by simpa only [List.take_succ_cons,List.drop_succ_cons,phase_cons] using h2⟩
    · have hc : len s d≤9 := by cases s <;> cases d <;> decide
      have hq : p+len s d<B+9 := by omega
      refine ⟨1,p+len s d,numerator s d p y/4,by simp,by omega,hq,?_,?_⟩
      · simpa using Trace.cons s d hd (Trace.nil (!s) _ _)
      · simpa [phase] using ht

/-- The margin conditions yield a crossing in an actual half-step trace. -/
theorem trace_barrier {s w p y P Y a k} (h : Trace s w p y P Y)
    (hy : 0<y) (hc : 3*y<p) (hv : valid s p)
    (hl : p+9*k≤a*4^k) (hh : a*4^k+8+18*k≤P) : ∃ b, b<9 ∧ Cross2 a b k := by
  obtain ⟨i,q,e,hi,hq,hq',hpre,hpost⟩ := rank_cross h (a*4^k) (by omega) (by omega)
  have hlen : (w.take i).length=i := by simp [Nat.min_eq_left hi]
  have hlen2 : (w.drop i).length=w.length-i := by simp
  have hr1 := trace_rank hpre
  have hr2 := trace_rank hpost
  have hk : k≤i := by omega
  have hk2 : 2*k≤w.length-i := by omega
  obtain ⟨r,t,hpre1,hpre2⟩ := trace_split hpre (i-k)
  obtain ⟨q2,e2,hpost1,hpost2⟩ := trace_split hpost k
  obtain ⟨q3,e3,hpost3,hpost4⟩ := trace_split hpost2 k
  obtain ⟨hs,hstrict⟩ := trace_strict hpre1 hy hc
  have hvalid := trace_valid hpre1 hv
  let b := q-a*4^k
  have hb' : b<9 := by dsimp [b]; omega
  have hqeq : q=a*4^k+b := by dsimp [b]; omega
  refine ⟨b,hb',phase s ((w.take i).take (i-k)),(w.take i).drop (i-k),(w.drop i).take k,((w.drop i).drop k).take k,
    r,t,e,q2,e2,q3,e3,?_,?_,?_,hs,hstrict,hvalid,?_,?_,?_⟩
  · simp [hlen]; omega
  · simp [hlen2,Nat.min_eq_left (show k≤w.length-i by omega)]
  · simp; omega
  · rwa [←hqeq]
  · have hphase : phase (phase s ((w.take i).take (i-k))) ((w.take i).drop (i-k))=phase s (w.take i) := by
      rw [←phase_append,List.take_append_drop]
    rwa [hphase,←hqeq]
  · have hphase : phase (phase s ((w.take i).take (i-k))) ((w.take i).drop (i-k))=phase s (w.take i) := by
      rw [←phase_append,List.take_append_drop]
    rwa [hphase]

theorem scale_exists (p : Nat) (hp : 0<p) : ∃ t, 4^t≤p ∧ p<4^(t+1) := by
  let t := p.log2/2
  have ht : 4^t=2^(2*t) := by rw [Nat.pow_mul]
  have ht' : 4^(t+1)=2^(2*(t+1)) := by rw [Nat.pow_mul]
  refine ⟨t,?_,?_⟩
  · rw [ht]; exact (Nat.le_log2 (by omega)).mp (by dsimp [t]; omega)
  · rw [ht']; exact (Nat.log2_lt (by omega)).mp (by dsimp [t]; omega)

private theorem scale_quadratic (t : Nat) (ht : 8≤t) : 256*(t+1)*(t+1)≤4^t := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases ht' : 8≤t
    · have h := ih ht'
      have hb : t+2≤2*(t+1) := by omega
      have hc := Nat.mul_le_mul hb hb
      rw [Nat.pow_succ]
      grind
    · have he : t=7 := by omega
      subst t
      decide

/-- Two adjacent powers-of-two provide a sufficient barrier with linear margins.
    Extra growth over rank doubling is 36(t+1)+8. -/
theorem rank_doubling_cover (t p P : Nat) (ht : 8≤t) (hl : 4^t≤p) (hh : p<4^(t+1))
    (hP : 2*p+36*(t+1)+8≤P) :
    ∃ a k, (a=1 ∨ a=2) ∧ 8≤k ∧ p+9*k≤a*4^k ∧ a*4^k+8+18*k≤P := by
  have hpow : 4^(t+1)=4*4^t := by rw [Nat.pow_succ]; omega
  have hquad := scale_quadratic t ht
  have hq : 9*(t+1)≤4^t := by
    have h := Nat.mul_le_mul_left (256*(t+1)) (show 1≤t+1 by omega)
    simp at h
    omega
  by_cases h₁ : p+9*t≤2*4^t
  · exact ⟨2,t,Or.inr rfl,ht,by simpa using h₁,by omega⟩
  by_cases h₂ : p+9*(t+1)≤4^(t+1)
  · exact ⟨1,t+1,Or.inl rfl,by omega,by simpa using h₂,by simp; omega⟩
  · exact ⟨2,t+1,Or.inr rfl,by omega,by omega,by omega⟩

/-- A long q0 path must cross a binary half-step rank barrier, with coefficient
    one or two. This removes all finite arithmetic gaps between powers of two. -/
theorem q0_cross (u : Nat) (hu : 1000000≤u) (h : Path (8*u+5) (24*u+22) (6*u+4)) :
    ∃ a k b, (a=1 ∨ a=2) ∧ 8≤k ∧ b<9 ∧ Cross2 a b k := by
  obtain ⟨w,P,Y,hw,htrace⟩ := RankBarrier.trace_of_path h
  obtain ⟨t,hl,hh⟩ := scale_exists (2*(24*u+22)) (by omega)
  have ht : 8≤t := by
    by_cases he : t<8
    · have hpow := Nat.pow_le_pow_right (n:=4) (by decide) (show t+1≤8 by omega)
      have hval : 4^8=65536 := by decide
      omega
    · omega
  have hquad := scale_quadratic t ht
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
  have hj : (18*(t+1)+11)*(t+1)≤w.length := by
    have hbound := Nat.mul_le_mul_right (t+1) (show 6*(18*(t+1)+11)≤256*(t+1) by omega)
    -- Reserve a constant margin as well; use 128 instead of 256.
    have hbound' := Nat.mul_le_mul_right (t+1) (show 6*(18*(t+1)+11)≤128*(t+1) by omega)
    have hsmall : 14≤128*(t+1)*(t+1) := by
      have := Nat.mul_le_mul_left (128*(t+1)) (show 1≤t+1 by omega)
      simp at this; omega
    rw [hw]
    grind
  have hextra := RankBarrier.extra_growth (k:=t+1) (j:=18*(t+1)+11) (by omega) htrace (by omega) (by omega) hP hj
  have hg : 2*(2*(24*u+22))+36*(t+1)+8≤2*P := by omega
  obtain ⟨a,k,ha,hk,h₁,h₂⟩ := rank_doubling_cover t _ (2*P) ht hl hh hg
  have ht' := expand_trace htrace
  obtain ⟨b,hb,hcross⟩ := trace_barrier ht' (by omega) (by omega) (by simp [valid,bit]) h₁ h₂
  exact ⟨a,k,b,ha,hk,hb,hcross⟩

theorem q0_of_no_binary_cross {Reach : Nat→Nat→Prop} (src : Source Reach)
    (hbar : ∀ a k b, (a=1 ∨ a=2) → 8≤k → b<9 → ¬ Cross2 a b k)
    {u n x y : Nat} (hu : 1000000≤u) (hn : n=23+32*u)
    (hx : x+24*u+19=13*2^n) (hy : y+13=2*x) : ¬ Reach x y := by
  intro hr
  obtain ⟨a,k,b,ha,hk,hb,hc⟩ := q0_cross u hu (q0_path src u n x y hn hx hy hr)
  exact hbar a k b ha hk hb hc

#print axioms q0_cross
#print axioms q0_of_no_binary_cross
end BB429Q0Macro.HalfStep
