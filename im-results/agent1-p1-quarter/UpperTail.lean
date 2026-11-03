import OddConeMass

namespace BB6.Agent1UpperTail
open BB6.Agent47P1
open BB6.Agent1Quarter

/-- The original source t=0 inverse halves the shifted left coordinate. -/
theorem inv0_halve (b d k c:Nat) (h:inverseAt b d 0 = some (k,c)) (hk:2≤k) :
    2*(2*k-4+12)=b+12 ∧ c+4=d+b/2+4 := by
  simp only [inverseAt] at h
  split at h
  · next hh =>
    obtain ⟨h1,h2⟩ := hh
    obtain ⟨hk',hc'⟩ := Prod.mk.inj (Option.some.inj h)
    omega
  · simp at h

/-- Consecutive genuine depth-zero odd inverse edges; includes the exact accumulated cost. -/
inductive UpperTail (b0 d0 m0 : Nat) : Nat → Nat → Nat → Nat → Prop where
  | root : UpperTail b0 d0 m0 b0 d0 m0 0
  | step (b d m n k c : Nat)
      (hprev : UpperTail b0 d0 m0 b d m n)
      (hb : 8 ≤ b) (hb4 : b % 4 = 0) (hd : d % 2 = 1)
      (hi : inverseAt b d 0 = some (k,c))
      (hk : 2 ≤ k) (hc : c % 2 = 1) :
      UpperTail b0 d0 m0 (2*k-4) (c+4) (m+1) (n+1)

/-- Exact dyadic left coordinate and inverse cost after any zero-depth tail. -/
theorem upper_tail_dyadic (b0 d0 m0 b d m n : Nat)
    (h : UpperTail b0 d0 m0 b d m n) :
    2^n*(b+12)=b0+12 ∧ m=m0+n := by
  induction h with
  | root => simp
  | step b d m n k c hprev hb hb4 hd hi hk hc ih =>
    obtain ⟨hpow,hcost⟩ := ih
    have hinv := inv0_halve b d k c hi hk
    constructor
    · rw [Nat.pow_succ]
      calc
        2^n*2*(2*k-4+12) = 2^n*(2*(2*k-4+12)) := by simp [Nat.mul_assoc]
        _ = 2^n*(b+12) := by rw [hinv.1]
        _ = b0+12 := hpow
    · omega

/-- A tail ending on an affine wall satisfies an exact dyadic Diophantine equation. -/
theorem upper_tail_wall (b0 d0 m0 b d m n q delta:Nat)
    (h : UpperTail b0 d0 m0 b d m n)
    (hwall : b=4*m+64*q+delta) :
    b0+12=2^n*(4*m0+4*n+64*q+delta+12) := by
  obtain ⟨hdy,hm⟩ := upper_tail_dyadic b0 d0 m0 b d m n h
  calc
    b0+12 = 2^n*(b+12) := hdy.symm
    _ = 2^n*(4*(m0+n)+64*q+delta+12) := by rw [hwall, hm]
    _ = 2^n*(4*m0+4*n+64*q+delta+12) := by congr 1; omega

/-- Every authentic odd inverse cone splits at its last positive-depth reset,
    or at the root if no such reset occurred. -/
theorem odd_cone_last_reset (b0 d0 b d m : Nat)
    (hcone : OddCone b0 d0 b d m) :
    ∃ B D M n,
      ((B=b0 ∧ D=d0 ∧ M=0) ∨
       ∃ bp dp mp t k c,
         OddCone b0 d0 bp dp mp ∧
         8≤bp ∧ bp%4=0 ∧ dp%2=1 ∧
         inverseAt bp dp t=some (k,c) ∧
         2≤k ∧ c%2=1 ∧ 1≤t ∧
         B=2*k-4 ∧ D=c+4 ∧ M=mp+t+1) ∧
      UpperTail B D M b d m n := by
  induction hcone with
  | root =>
      exact ⟨b0,d0,0,0,Or.inl ⟨rfl,rfl,rfl⟩,UpperTail.root⟩
  | parent bp dp mp t k c hprev hb hb4 hd hi hk hc ih =>
    cases t with
    | zero =>
      obtain ⟨B,D,M,n,hstart,htail⟩ := ih
      exact ⟨B,D,M,n+1,hstart,
        UpperTail.step bp dp mp n k c htail hb hb4 hd (by simpa using hi) hk hc⟩
    | succ t =>
      refine ⟨2*k-4,c+4,mp+(t+1)+1,0,Or.inr ?_,UpperTail.root⟩
      exact ⟨bp,dp,mp,t+1,k,c,hprev,hb,hb4,hd,hi,hk,hc,by omega,rfl,rfl,rfl⟩

/-- Full-cone affine-wall witnesses satisfy a source-true last-reset equation,
    with no restriction on cone depth, budget, or initial parameters. -/
theorem odd_cone_wall_last_reset (b0 d0 b d m q delta : Nat)
    (hcone : OddCone b0 d0 b d m)
    (hwall : b=4*m+64*q+delta) :
    ∃ B D M n,
      ((B=b0 ∧ D=d0 ∧ M=0) ∨
       ∃ bp dp mp t k c,
         OddCone b0 d0 bp dp mp ∧
         8≤bp ∧ bp%4=0 ∧ dp%2=1 ∧
         inverseAt bp dp t=some (k,c) ∧
         2≤k ∧ c%2=1 ∧ 1≤t ∧
         B=2*k-4 ∧ D=c+4 ∧ M=mp+t+1) ∧
      B+12=2^n*(4*M+4*n+64*q+delta+12) := by
  obtain ⟨B,D,M,n,hstart,htail⟩ := odd_cone_last_reset b0 d0 b d m hcone
  refine ⟨B,D,M,n,hstart,?_⟩
  exact upper_tail_wall B D M b d m n q delta htail hwall

#print axioms odd_cone_wall_last_reset
#print axioms upper_tail_wall
end BB6.Agent1UpperTail
