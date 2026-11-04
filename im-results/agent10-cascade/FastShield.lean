import ManyShield

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CascadeFastShield
open CascadeSource CascadeManyShield

/-- The fatal-height scale dominates the linear offset at every index. -/
private theorem n_exp_lower : ∀ n : Nat, n+4 ≤ 4*2^n := by
  intro n
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    omega

/-- Quantified exponential margin needed to recover n from c_n. -/
private theorem n_exp_half : ∀ n : Nat, 2 ≤ n → n+4 ≤ 2^(n+1) := by
  intro n hn
  have h : ∀ k : Nat, k+6 ≤ 2^(k+3) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      rw [show k+1+3=k+3+1 by omega, Nat.pow_succ]
      omega
  have h':n=(n-2)+2 := by omega
  have hh:= h (n-2)
  rw [h']
  simpa [show (n-2)+2+1=(n-2)+3 by omega] using hh

/-- Fatal c_n has binary logarithm precisely n+1 for every n>=2. -/
theorem fatal_log2 (n : Nat) (hn : 2≤n) :
  Nat.log2 (fatal n) = n+1 := by
  have hh:=n_exp_half n hn
  have hbig :=n_exp_lower n
  have hp : 1 ≤ 2^n := Nat.one_le_pow n 2 (by decide)
  have he1 : 2^(n+1)=2*2^n := by rw [Nat.pow_succ]; omega
  have he2 : 2^(n+2)=4*2^n := by
    rw [show n+2=n+1+1 by omega, Nat.pow_succ, he1]
    omega
  have hle : 2^(n+1) ≤ fatal n := by
    dsimp [fatal]
    omega
  have hlt : fatal n < 2^(n+2) := by
    dsimp [fatal]
    omega
  have hz : fatal n ≠ 0 := by omega
  exact (Nat.log2_eq_iff hz).mpr ⟨hle, by simpa using hlt⟩

/-- Exact O(log h) membership predicate for the bounded fatal family. -/
def badFast (bound : Nat) (s : Nat × Nat) : Bool :=
  let n := s.1.log2 - 1
  decide (s.2=0 ∧ 4≤n ∧ n≤bound ∧
    (n%6=4∨n%6=5) ∧ s.1=fatal n)

theorem badFast_hits (N n : Nat) (hn:4≤n) (ht:n≤N)
 (hc:n%6=4∨n%6=5) : badFast N (fatal n,0)=true := by
  simp [badFast, fatal_log2 n (by omega), hn, ht, hc]

private theorem fatal_mono_step (n:Nat): fatal n ≤ fatal (n+1) := by
  have hh:=n_exp_lower n
  have hpow : 2^(n+1)=2*2^n := by rw [Nat.pow_succ]; omega
  have hp : 1≤2^n := Nat.one_le_pow n 2 (by decide)
  dsimp [fatal]
  omega

theorem fatal_mono (n N:Nat) (h:n≤N): fatal n ≤ fatal N := by
  induction N with
  | zero =>
    have h0 : n=0 := by omega
    simp [h0]
  | succ N ih =>
    by_cases hl:n≤N
    · exact Nat.le_trans (ih hl) (fatal_mono_step N)
    · have he:n=N+1:=by omega
      rw [he]
      exact Nat.le_refl _

/-- Generic root exclusion for every bounded index family, with finite
    proof certificate and symbolic coverage over all n <= N. -/
theorem fast_root_excludes (N fuel n : Nat) (hn:4≤n) (ht:n≤N)
    (hc:n%6=4∨n%6=5)
    (hcert:shieldMany (badFast N) (2*fatal N) fuel (2,0)=true) :
    ¬Orbit (2,0) (fatal n,0) := by
  have hb := badFast_hits N n hn ht hc
  have hm : mass (fatal n,0) ≤ 2*fatal N := by
    have hh:=fatal_mono n N ht
    dsimp [mass]; omega
  exact shieldMany_sound (badFast N) (2*fatal N) fuel (2,0)
      (fatal n,0) hb hm hcert

/-- Every surviving fatal reset through index 256 is globally absent.
    Uses ordinary Lean kernel reduction, without native_decide axioms. -/
theorem blank_excludes_surviving_through_256 (n : Nat)
    (hn : 4 ≤ n) (ht : n ≤ 256) (hc : n%6=4 ∨ n%6=5) :
    ¬Orbit (2,0) (fatal n,0) := by
  set_option maxRecDepth 600000 in
    exact fast_root_excludes 256 39000 n hn ht hc (by decide)

#print axioms fatal_log2
#print axioms fast_root_excludes
#print axioms blank_excludes_surviving_through_256
end CascadeFastShield
