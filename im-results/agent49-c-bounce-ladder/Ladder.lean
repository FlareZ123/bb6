import JumpHigh
import Lean.Elab.Tactic.Omega

namespace BB6.Agent49
open BB6.Agent46 (run run_high)
abbrev S := Nat × Nat × Nat

theorem run_add (n m : Nat) (s : Option S) :
    run (n+m) s = run m (run n s) := by
  induction n generalizing s with
  | zero => rw [Nat.zero_add]; rfl
  | succ n ih =>
      rw [Nat.succ_add]
      change run (n+m) (s.bind BB6CLine.nextC) =
        run m (run n (s.bind BB6CLine.nextC))
      exact ih _

private theorem odd_high_start (k c : Nat) (hk : k%2=1) (hc : 4≤c) :
    BB6CLine.nextC (0,k,c)=some (2*k+3,0,c) := by
  obtain ⟨d,rfl⟩ : ∃ d, c=d+4 := ⟨c-4,by omega⟩
  have hne : k%2 ≠ 0 := by omega
  have hdiv : k%2+2*(k/2)=k := Nat.mod_add_div k 2
  simp only [BB6CLine.nextC,hne,ite_false,Option.some.injEq, Prod.mk.injEq]
  constructor
  · omega
  · trivial

/-- Exact odd-middle bounce returning to a zero-left state. -/
theorem odd_full_bounce (k c : Nat) (hk : k%2=1) (hc : 2*k+6≤c) :
    run (2*k+4) (some (0,k,c)) = some (0,2*k+3,c-(2*k+3)) := by
  have hfirst := odd_high_start k c hk (by omega)
  have hhigh := run_high (2*k+3) (2*k+3) 0 c (by omega) (by omega)
  have hn : 2*k+4=(2*k+3)+1 := by omega
  rw [hn]
  change run (2*k+3) ((some (0,k,c)).bind BB6CLine.nextC) = _
  simp only [Option.bind_some,hfirst]
  rw [hhigh]
  simp only [Option.some.injEq,Prod.mk.injEq]
  simp

/-- Middle counter after n full odd bounce cycles. -/
def K (k : Nat) : Nat → Nat
  | 0 => k
  | n+1 => 2*K k n+3

/-- Third-counter depletion after n full cycles. -/
def D (k : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => D k n + 2*K k n+3

/-- Number of original accelerated CLine calls after n full cycles. -/
def T (k : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => T k n + 2*K k n+4

theorem K_odd (k n : Nat) (hk : k%2=1) : K k n %2=1 := by
  induction n with
  | zero => simpa [K] using hk
  | succ n ih => simp [K]

theorem K_closed (k n : Nat) : K k n+3=(k+3)*2^n := by
  induction n with
  | zero => simp [K]
  | succ n ih =>
      calc
        K k (n+1)+3=2*(K k n+3) := by simp [K]; omega
        _=2*((k+3)*2^n) := by rw [ih]
        _=(k+3)*2^(n+1) := by simp only [Nat.pow_succ]; ac_rfl

theorem D_conservation (k n : Nat) : D k n+3*n+2*k=2*K k n := by
  induction n with
  | zero => simp [K,D]
  | succ n ih =>
      simp only [D,K]
      omega

theorem T_conservation (k n : Nat) : T k n+2*n+2*k=2*K k n := by
  induction n with
  | zero => simp [K,T]
  | succ n ih =>
      simp only [T,K]
      omega

theorem time_eq_deduction_plus_n (k n : Nat) : T k n = D k n+n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [T,D]
      omega

/-- A universally quantified exact high-bounce ladder, with the last endpoint
remaining in the c>=4 corridor. -/
theorem odd_ladder (k c n : Nat) (hk : k%2=1) (hc : D k n+4≤c) :
    run (T k n) (some (0,k,c)) = some (0,K k n,c-D k n) := by
  induction n with
  | zero => simp [T,K,D,run]
  | succ n ih =>
      have hsmall : D k n+4≤c := by
        simp only [D] at hc
        omega
      have hmid : 2*K k n+6≤c-D k n := by
        simp only [D] at hc
        omega
      have hprefix := ih hsmall
      have hstep := odd_full_bounce (K k n) (c-D k n) (K_odd k n hk) hmid
      have ht : T k (n+1)=T k n+(2*K k n+4) := by simp only [T]; omega
      rw [ht,run_add,hprefix,hstep]
      simp only [K,D,Option.some.injEq,Prod.mk.injEq]
      constructor
      · trivial
      · constructor
        · trivial
        · omega

#print axioms odd_full_bounce
#print axioms odd_ladder
#print axioms K_closed
#print axioms D_conservation
#print axioms T_conservation
#print axioms time_eq_deduction_plus_n
end BB6.Agent49
