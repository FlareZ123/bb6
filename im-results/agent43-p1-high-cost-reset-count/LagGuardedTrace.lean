import LagGuarded

namespace BB6.Agent43LagExact
open BB6.Agent45.DelayedCarry
open BB6.P1CarryExact (Micro LegalGap)

def rightAt (n i B a : Nat) : Nat := quotient n i B-a
def leftAt (n i B a : Nat) : Nat := total n-(n+i+1)-rightAt n i B a

theorem coords_eq (n i B a v w : Nat) (hn : 14≤n)
    (h : Micro n i v w) (hq : v+a=quotient n i B) :
    rightAt n i B a=v ∧ leftAt n i B a=w := by
  have hm := BB6.P1CarryExact.micro_mass n i v w hn h
  change v+w+n+i+1=total n at hm
  unfold leftAt rightAt
  omega

theorem trace_coords (n i B a : Nat) (hn : 14≤n) (heven : n%2=0)
    (h : Trace n i B a) :
    Micro n i (rightAt n i B a) (leftAt n i B a) ∧
    rightAt n i B a+a=quotient n i B ∧
    rightAt n i B a+leftAt n i B a+n+i+1=total n := by
  obtain ⟨v,w,hM,_,_,hq⟩ := trace_micro_exact n i B a hn heven h
  obtain ⟨hv,hw⟩ := coords_eq n i B a v w hn hM hq
  rw [hv,hw]
  exact ⟨hM,hq,BB6.P1CarryExact.micro_mass n i v w hn hM⟩

/-- The small carry word augmented by exactly the unit-cost source guards.
    The terminal left bound is tested separately to close the final gap. -/
inductive GuardedTrace (n : Nat) : Nat → Nat → Nat → Prop
  | first : GuardedTrace n 1 1 ((n+2)/2)
  | step (i B a x c : Nat) (h : GuardedTrace n i B a) (hx : x≤1)
      (he : 2*c+target n i B=a+x*(n+i+3))
      (hs : x=1 → 10≤leftAt n i B a)
      (hc : 2≤rightAt n (i+1) (B+2^i*x) c) :
      GuardedTrace n (i+1) (B+2^i*x) c

theorem guarded_trace_trace {n i B a : Nat} (h : GuardedTrace n i B a) :
    Trace n i B a := by
  induction h with
  | first => exact Trace.first
  | step i B a x c h hx he hs hc ih => exact Trace.step i B a x c ih hx he

theorem guarded_trace_to_micro {n i B a : Nat} (hn : 14≤n) (heven : n%2=0)
    (h : GuardedTrace n i B a) :
    GuardedMicro n i (rightAt n i B a) (leftAt n i B a) := by
  have hT := BB6.Agent45.DelayedCarry.total_even n (by omega)
  have hlarge := BB6.P1CarryExact.pow2_ge_1100_mul n hn
  have hbig : n+12≤total n := by unfold total; omega
  induction h with
  | first =>
    let p := (total n-n-2)/2
    have hp : 2*p+n+2=total n := by dsimp [p]; omega
    have hG : GuardedMicro n 1 p p := by
      apply GuardedMicro.one 0 1 (BB6.P1CarryExact.total n-n-2) p p GuardedMicro.root
      · change 10≤total n-n-2
        omega
      · omega
      · change 1+total n=2*p+(n+0+3)
        omega
      · change total n-n-2=2*p
        omega
    have hQ : p+(n+2)/2=quotient n 1 1 := by simp [quotient] <;> omega
    obtain ⟨hv,hw⟩ := coords_eq n 1 1 ((n+2)/2) p p hn (guarded_micro hG) hQ
    rw [hv,hw]
    exact hG
  | step i B a x c h hx he hs hc ih =>
    have ht := guarded_trace_trace h
    have hi := (trace_bounds n i B a ht).1
    obtain ⟨_,hq0,hm0⟩ := trace_coords n i B a hn heven ht
    have ht' := Trace.step i B a x c ht hx he
    obtain ⟨_,hq1,hm1⟩ := trace_coords n (i+1) (B+2^i*x) c hn heven ht'
    have hrem : (quotient n i B+total n*x)%2=target n i B := by
      rw [target_eq,Nat.add_mod,Nat.mul_mod,hT]
      simp
    have hqstep := quotient_step n i B x
    have hsum : 2*quotient n (i+1) (B+2^i*x)+target n i B=
        quotient n i B+total n*x := by omega
    rcases (show x=0∨x=1 by omega) with rfl|rfl
    · simp only [Nat.mul_zero,Nat.zero_mul,Nat.add_zero] at he hsum hq1 hm1 hc ⊢
      apply GuardedMicro.zero i _ _ _ _ ih hi hc
      · omega
      · change leftAt n i B a+total n=2*leftAt n (i+1) B c+(n+i+3)
        omega
    · simp only [Nat.mul_one,Nat.one_mul] at he hsum hq1 hm1 hc ⊢
      apply GuardedMicro.one i _ _ _ _ ih (hs rfl) hc
      · change rightAt n i B a+total n=2*rightAt n (i+1) (B+2^i) c+(n+i+3)
        omega
      · omega

theorem guarded_micro_to_trace {n i v w : Nat} (hn : 14≤n) (heven : n%2=0)
    (h : GuardedMicro n i v w) (hi : 0<i) :
    ∃ B a, GuardedTrace n i B a ∧ v+a=quotient n i B := by
  induction h with
  | root => omega
  | one m v w u z h hs hu hv hw ih =>
    by_cases h0 : m=0
    · subst m
      cases h with
      | root =>
        change 1+total n=2*u+(n+0+3) at hv
        refine ⟨1,(n+2)/2,GuardedTrace.first,?_⟩
        simp [quotient] <;> omega
    · obtain ⟨B,a,ht,hq⟩ := ih (by omega)
      have hv' : 2*u+1*(n+m+3)=v+total n*1 := by simpa using hv.symm
      obtain ⟨c,hstep,hQ⟩ := lift_quotient n m B a v u 1 (by omega) hq hv'
      have he0 := coords_eq n m B a v w hn (guarded_micro h) hq
      have hG := GuardedMicro.one m v w u z h hs hu hv hw
      have he1 := coords_eq n (m+1) (B+2^m*1) c u z hn (guarded_micro hG) hQ
      refine ⟨B+2^m*1,c,GuardedTrace.step m B a 1 c ht (by decide) hstep ?_ ?_,hQ⟩
      · intro _
        rw [he0.2]
        exact hs
      · rw [he1.1]
        exact hu
  | zero m v w u z h hm hu hv hw ih =>
    obtain ⟨B,a,ht,hq⟩ := ih hm
    have hv' : 2*u+0*(n+m+3)=v+total n*0 := by simpa using hv.symm
    obtain ⟨c,hstep,hQ⟩ := lift_quotient n m B a v u 0 (by omega) hq hv'
    have hG := GuardedMicro.zero m v w u z h hm hu hv hw
    have he1 := coords_eq n (m+1) (B+2^m*0) c u z hn (guarded_micro hG) hQ
    refine ⟨B+2^m*0,c,GuardedTrace.step m B a 0 c ht (by decide) hstep ?_ ?_,hQ⟩
    · intro hx
      omega
    · rw [he1.1]
      exact hu

/-- Positive-cost legal inverse histories are EXACTLY guarded delayed
    traces with the recovered endpoint and the final left guard. -/
theorem legal_iff_guarded_trace (n i v w : Nat) (hn : 14≤n) (heven : n%2=0) :
    (LegalGap n i v w ∧ 0<i) ↔
    ∃ B a, GuardedTrace n i B a ∧ v=rightAt n i B a ∧
      w=leftAt n i B a ∧ 6≤w := by
  constructor
  · rintro ⟨h,hi⟩
    obtain ⟨hG,hW⟩ := (legal_iff_guarded hn).mp h
    obtain ⟨B,a,ht,hQ⟩ := guarded_micro_to_trace hn heven hG hi
    obtain ⟨hv,hw⟩ := coords_eq n i B a v w hn (guarded_micro hG) hQ
    exact ⟨B,a,ht,hv.symm,hw.symm,by omega⟩
  · rintro ⟨B,a,ht,hv,hw,hW⟩
    have hG := guarded_trace_to_micro hn heven ht
    rw [←hv,←hw] at hG
    exact ⟨(legal_iff_guarded hn).mpr ⟨hG,Or.inr hW⟩,
      (trace_bounds n i B a (guarded_trace_trace ht)).1⟩

#print axioms legal_iff_guarded_trace
end BB6.Agent43LagExact
