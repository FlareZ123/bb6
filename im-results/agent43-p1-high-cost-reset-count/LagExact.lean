import LagMicro

namespace BB6.Agent43LagExact
open BB6.Agent45.DelayedCarry
open BB6.P1CarryExact (Micro)

/-- The delayed arithmetic abstraction is exact at every depth, not just
    before the delayed digits arrive. Both original microcoordinates are
    strictly positive. -/
theorem trace_micro_exact (n m B a : Nat) (hn : 14 ≤ n) (heven : n%2=0)
    (h : Trace n m B a) :
    ∃ v w, Micro n m v w ∧ 0<v ∧ 0<w ∧ v+a=quotient n m B := by
  have hT := BB6.Agent45.DelayedCarry.total_even n (by omega)
  have hlarge := BB6.P1CarryExact.pow2_ge_1100_mul n hn
  have hbig : n+3 < total n := by unfold total; omega
  induction h with
  | first =>
    let v := (total n-n-2)/2
    have hv : 2*v+n+2=total n := by dsimp [v]; omega
    have hp : 0<v := by omega
    have hm : Micro n 1 v v := by
      apply Micro.one 0 1 (BB6.P1CarryExact.total n-n-2) v v Micro.root
      · change 1+total n=2*v+(n+0+3)
        omega
      · change total n-n-2=2*v
        omega
    refine ⟨v,v,hm,hp,hp,?_⟩
    simp [quotient] <;> omega
  | step i B a x c h hx he ih =>
    obtain ⟨v,w,hM,hv,hw,hq⟩ := ih
    have hmass := BB6.P1CarryExact.micro_mass n i v w hn hM
    change v+w+n+i+1=total n at hmass
    have hW : n+i+3≤total n := by omega
    have hi := (trace_bounds n i B a h).1
    have hrem : (quotient n i B+total n*x)%2=target n i B := by
      rw [target_eq,Nat.add_mod,Nat.mul_mod,hT]
      simp
    have hqstep := quotient_step n i B x
    have hsum : 2*quotient n (i+1) (B+2^i*x)+target n i B=
        quotient n i B+total n*x := by omega
    rcases (show x=0∨x=1 by omega) with rfl|rfl
    · simp only [Nat.mul_zero,Nat.zero_mul,Nat.add_zero] at he hsum ⊢
      let u := v/2
      let z := (w+total n-(n+i+3))/2
      have hU : v=2*u := by dsimp [u]; omega
      have hZ : w+total n=2*z+(n+i+3) := by dsimp [z]; omega
      have hu : 0<u := by omega
      have hz : 0<z := by omega
      refine ⟨u,z,Micro.zero i v w u z hM (by omega) hU hZ,hu,hz,?_⟩
      omega
    · simp only [Nat.mul_one,Nat.one_mul] at he hsum ⊢
      let u := (v+total n-(n+i+3))/2
      let z := w/2
      have hU : v+total n=2*u+(n+i+3) := by dsimp [u]; omega
      have hZ : w=2*z := by dsimp [z]; omega
      have hu : 0<u := by omega
      have hz : 0<z := by omega
      refine ⟨u,z,Micro.one i v w u z hM hU hZ,hu,hz,?_⟩
      omega

/-- A trace determines both microcoordinates exactly. The mass and
    quotient equations suffice for the converse endpoint test. -/
theorem trace_micro_iff (n m v w : Nat) (hn : 14≤n) (heven : n%2=0) :
    (Micro n m v w ∧ 0<m) ↔
    ∃ B a, Trace n m B a ∧ v+a=quotient n m B ∧
        v+w+n+m+1=total n := by
  constructor
  · rintro ⟨h,hm⟩
    obtain ⟨B,a,ht,hq,_⟩ := micro_trace n m v w hn heven h hm
    exact ⟨B,a,ht,hq,BB6.P1CarryExact.micro_mass n m v w hn h⟩
  · rintro ⟨B,a,ht,hq,hm⟩
    obtain ⟨u,z,hM,_,_,hQ⟩ := trace_micro_exact n m B a hn heven ht
    have hmass := BB6.P1CarryExact.micro_mass n m u z hn hM
    change u+z+n+m+1=total n at hmass
    have huv : u=v := by omega
    have hzw : z=w := by omega
    subst u
    subst z
    exact ⟨hM,(trace_bounds n m B a ht).1⟩

/-- The delayed trace cannot persist for arbitrarily many positions even
    when the bit word is completely aperiodic. -/
theorem trace_cost_le (n m B a : Nat) (hn : 14≤n) (heven : n%2=0)
    (h : Trace n m B a) : m+n+3≤total n := by
  obtain ⟨v,w,hM,hv,hw,_⟩ := trace_micro_exact n m B a hn heven h
  have hm := BB6.P1CarryExact.micro_mass n m v w hn hM
  change v+w+n+m+1=total n at hm
  omega

theorem trace_at_cap (n m B a : Nat) (hn : 14≤n) (heven : n%2=0)
    (h : Trace n m B a) (hcap : m+n+3=total n) :
    Micro n m 1 1 ∧ 1+a=quotient n m B := by
  obtain ⟨v,w,hM,hv,hw,hq⟩ := trace_micro_exact n m B a hn heven h
  have hm := BB6.P1CarryExact.micro_mass n m v w hn hM
  change v+w+n+m+1=total n at hm
  have h1 : v=1 := by omega
  have h2 : w=1 := by omega
  simpa [h1,h2] using And.intro hM hq

#print axioms trace_micro_exact
#print axioms trace_micro_iff
#print axioms trace_cost_le
#print axioms trace_at_cap
end BB6.Agent43LagExact
