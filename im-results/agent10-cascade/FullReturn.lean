import ExactGate
import ValuationDrain

namespace CascadeResetInverse
open CascadeSource CascadeSweep

private def A (k : Nat) : Nat := 4*2^k-2
private def B (h k : Nat) : Nat := 2*h+2*k+9-8*2^k

private theorem reach_trans {x y z : Nat × Nat} (hxy : ReachC x y) (hyz : ReachC y z) :
    ReachC x z := by
  induction hyz with
  | refl => exact hxy
  | push hr he ih => exact ReachC.push ih he

private def failed (h k : Nat) : Prop := h+k+5<8*2^k

private theorem exp_linear (n : Nat) : n+1≤2^n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

private theorem fail_eventually (h : Nat) : failed h (h+10) := by
  have he := exp_linear (h+10)
  dsimp [failed]
  omega

private theorem minimal_fail_at_most (h b : Nat)
    (hb : failed h b) :
    ∃k, k≤b ∧ failed h k ∧ ∀ j, j<k → ¬failed h j := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    classical
    by_cases hprev : ∃j, j<b ∧ failed h j
    · obtain ⟨j,hjb,hj⟩ := hprev
      obtain ⟨k,hk,hfail,hmin⟩ := ih j hjb hj
      exact ⟨k,by omega,hfail,hmin⟩
    · exact ⟨b,by omega,hb,by
        intro j hj hfail
        exact hprev ⟨j,hj,hfail⟩⟩

/-- The doubling sweep has a unique first failed guard at finite k. -/
theorem first_fail (h : Nat) :
    ∃ k, (∀ j, j<k → 8*2^j≤h+j+5) ∧ h+k+5<8*2^k := by
  obtain ⟨k,hkle,hfk,hmin⟩ :=
    minimal_fail_at_most h (h+10) (fail_eventually h)
  refine ⟨k,?_,hfk⟩
  intro j hj
  by_cases hyes : 8*2^j≤h+j+5
  · exact hyes
  · exfalso
    have hf : failed h j := by dsimp [failed]; omega
    exact hmin j hj hf

/-- The last enabled guard bounds the first failing sweep counter below. -/
theorem first_low (h k : Nat)
    (hg : ∀ j, j<k → 8*2^j≤h+j+5) :
    4*2^k≤h+k+4 := by
  cases k with
  | zero => simp
  | succ k =>
    have hp := hg k (by omega)
    rw [Nat.pow_succ]
    omega

/-- Every actually enabled initial sweep phase has a certified reachable C-state. -/
theorem sweep_prefix (h k : Nat)
  (hg : ∀ j, j<k → 8*2^j≤h+j+5) :
  ReachC (h,0) (A k,B h k) := by
  induction k with
  | zero =>
    have he : Cstep h 0 = some (A 0,B h 0) := by
      simp [Cstep,A,B]
    exact ReachC.push (ReachC.refl _) he
  | succ k ih =>
    have hprev : ReachC (h,0) (A k,B h k) :=
      ih (by intro j hj; exact hg j (by omega))
    have hguard : 8*2^k≤h+k+5 := hg k (by omega)
    have hnext : Cstep (A k) (B h k) = some (A (k+1), B h (k+1)) := by
      have he := CascadeExactGate.cascade_one h k hguard
      change Cstep (4*2^k-2) (2*h+2*k+9-8*2^k) =
        some (4*2^(k+1)-2, 2*h+2*(k+1)+9-8*2^(k+1)) at he
      exact he
    exact ReachC.push hprev hnext

/-- A first failed sweep guard with nonfatal even counter reaches its reset. -/
theorem even_reset (h k : Nat)
  (hg : ∀ j, j<k → 8*2^j≤h+j+5)
  (hlow : 4*2^k≤h+k+4)
  (hhigh : h+k+5<8*2^k)
  (hnot : h+k+4≠4*2^k)
  (hpar : (h+k)%2=0) :
  ReachC (h,0) (4*2^k+(h+k)/2,0) := by
  have hp : 1≤2^k := Nat.one_le_pow k 2 (by decide)
  have he := exit (2^k) h k hp hlow hhigh hnot
  have hprefix := sweep_prefix h k hg
  have he' : Cstep (A k) (B h k) = some (4*2^k+(h+k)/2,0) := by
    simpa [A,B,hpar] using he
  exact ReachC.push hprefix he'

/-- The same first-failure guard followed by a valuation-length odd drain. -/
theorem odd_reset (h k t d : Nat)
  (hg : ∀ j, j<k → 8*2^j≤h+j+5)
  (hlow : 4*2^k≤h+k+4)
  (hhigh : h+k+5<8*2^k)
  (hnot : h+k+4≠4*2^k)
  (hpar : (h+k)%2=1)
  (hfactor : 4*2^k+(h+k)/2+3=2^t*d)
  (hd : d%2=1) :
  ReachC (h,0) ((3^(t+1)*d-5)/2,0) := by
  have hp : 1≤2^k := Nat.one_le_pow k 2 (by decide)
  have he := exit (2^k) h k hp hlow hhigh hnot
  have hprefix := sweep_prefix h k hg
  have he' : Cstep (A k) (B h k) = some (2^t*d-3,2) := by
    have hfirst : 2^t*d-3=4*2^k+(h+k)/2 := by omega
    simpa [A,B,hpar,hfirst] using he
  have hq : 4≤2^t*d := by omega
  exact reach_trans (ReachC.push hprefix he') (drain_power t d hd hq)

/-- The first failed guard is a halt exactly when its C right-counter is one. -/
theorem fatal_first_exit (h k : Nat)
  (hg : ∀ j, j<k → 8*2^j≤h+j+5)
  (hfat : h+k+4=4*2^k) :
  ReachC (h,0) (A k,1) ∧ Cstep (A k) 1 = none := by
  have hprefix := sweep_prefix h k hg
  have hbk : B h k=1 := by
    dsimp [B]
    omega
  constructor
  · simpa [hbk] using hprefix
  · simp [Cstep]

/-- Pure arithmetic existence of the 2-adic odd factor needed by the exact
    closed drain formula, for every strictly positive input. -/
theorem factor_twos (q : Nat) (hq : 0<q) :
  ∃ t d, q=2^t*d ∧ d%2=1 := by
  induction q using Nat.strongRecOn with
  | ind q ih =>
    by_cases hodd : q%2=1
    · exact ⟨0,q,by simp,hodd⟩
    · have heven : q%2=0 := by omega
      have hq2 : 0<q/2 := by omega
      have hlt : q/2<q := by omega
      obtain ⟨t,d,heq,hd⟩ := ih (q/2) hlt hq2
      refine ⟨t+1,d,?_,hd⟩
      have hmul : q=2*(q/2) := by omega
      rw [hmul,heq,Nat.pow_succ]
      simp only [Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm]

/-- A complete universal source-C first-sweep exit: every reset input has
    a finite, exactly prescribed successful return or reaches the fatal B=1
    terminal. Its b=2 branch has arbitrary valuation depth, handled in Lean. -/
theorem all_exits (h : Nat) :
  ∃ k,
    (ReachC (h,0) (A k,1) ∧ Cstep (A k) 1 = none) ∨
    ReachC (h,0) (4*2^k+(h+k)/2,0) ∨
    ∃ t d, d%2=1 ∧ 4*2^k+(h+k)/2+3=2^t*d ∧
      ReachC (h,0) ((3^(t+1)*d-5)/2,0) := by
  obtain ⟨k,hg,hhigh⟩ := first_fail h
  have hlow := first_low h k hg
  refine ⟨k,?_⟩
  by_cases hfat : h+k+4=4*2^k
  · exact Or.inl (fatal_first_exit h k hg hfat)
  · by_cases hpar : (h+k)%2=0
    · exact Or.inr (Or.inl (even_reset h k hg hlow hhigh hfat hpar))
    · have hodd : (h+k)%2=1 := by omega
      have hq : 0<4*2^k+(h+k)/2+3 := by omega
      obtain ⟨t,d,heq,hd⟩ := factor_twos _ hq
      exact Or.inr (Or.inr ⟨t,d,hd,heq,
        odd_reset h k t d hg hlow hhigh hfat hodd heq hd⟩)

#print axioms fatal_first_exit
#print axioms factor_twos
#print axioms all_exits
#print axioms first_fail
#print axioms first_low
#print axioms sweep_prefix
#print axioms even_reset
#print axioms odd_reset
end CascadeResetInverse
