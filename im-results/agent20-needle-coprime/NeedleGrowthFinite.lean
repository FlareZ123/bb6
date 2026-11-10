import NeedleGrowth
import Lean.Elab.Tactic.Omega

namespace NeedleGrowth

/-- A finite trajectory prefix, with every indicated edge successful. -/
def Prefix (f : Nat → Nat) (N : Nat) : Prop :=
  ∀ i, i < N → Edge (f i) (f (i+1))

/-- The base linear lower bound is valid even if the trajectory later halts. -/
theorem prefix_linear (f : Nat → Nat) (N : Nat) (h : Prefix f N)
    (n : Nat) (hn : n ≤ N) : f 0 + n ≤ f n := by
  induction n with
  | zero => omega
  | succ n ih =>
      have hin : n ≤ N := by omega
      rcases h n (by omega) with ⟨q,v,_,hh⟩
      have hb : f n+1 ≤ f (n+1) := by rw [hh]; omega
      have hr := ih hin
      omega

/-- Drift through a dyadic region holds on finite surviving prefixes. -/
theorem prefix_dyadic_drift (f : Nat → Nat) (N M n t : Nat)
    (h : Prefix f N) (hM : 2^M ≤ f n) (ht : n+t ≤ N) :
    f n + t*(M+2) ≤ f (n+t) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have htpre : n+t ≤ N := by omega
      have hgrowth := ih htpre
      have hMnext : 2^M ≤ f (n+t) := by omega
      rcases h (n+t) (by omega) with ⟨q,v,hfactor,hnext⟩
      have hg := dyadic_increment q v M (by rw [←hfactor]; exact hMnext)
      have hstep : f (n+t)+M+2 ≤ f (n+t+1) := by
        rw [hnext]
        omega
      calc
        f n+(t+1)*(M+2) = (f n+t*(M+2))+(M+2) := by rw [Nat.add_mul]; omega
        _ ≤ f (n+t)+(M+2) := by omega
        _ ≤ f (n+(t+1)) := by
          have hi : n+(t+1) = n+t+1 := by omega
          rw [hi]
          omega

/-- Every finite successful trajectory prefix has superlinear growth in
    its number of completed high-level steps, with no nonhalting premise. -/
theorem prefix_superlinear (f : Nat → Nat) (N M n : Nat)
    (h : Prefix f N) (hn : n ≤ N) (hlarge : 2^(M+1) ≤ n) :
    (n/2)*(M+2) ≤ f n := by
  have hpow : 2^(M+1)=2^M*2 := by rw [Nat.pow_succ]
  have hthreshold := prefix_linear f N h (2^M) (by omega)
  have hstart : 2^M ≤ f (2^M) := by omega
  have hdrift := prefix_dyadic_drift f N M (2^M) (n-2^M) h hstart (by omega)
  have hindex : 2^M+(n-2^M)=n := by omega
  rw [hindex] at hdrift
  have hhalf : n/2 ≤ n-2^M := by omega
  have hmult := Nat.mul_le_mul_right (M+2) hhalf
  have hcomm : (n-2^M)*(M+2) = (M+2)*(n-2^M) := Nat.mul_comm _ _
  omega

#print axioms NeedleGrowth.prefix_linear
#print axioms NeedleGrowth.prefix_dyadic_drift
#print axioms NeedleGrowth.prefix_superlinear
end NeedleGrowth

namespace NeedleGrowth

/-- Closed-form superlinear prefix lower bound in terms of the number
    of executed successful high-level steps. -/
theorem prefix_log_growth (f : Nat → Nat) (N n : Nat)
    (h : Prefix f N) (hn : n ≤ N) (h2 : 2 ≤ n) :
    (n/2)*(Nat.log2 n+1) ≤ f n := by
  have hne : n ≠ 0 := by omega
  have hlog := (Nat.log2_eq_iff hne).mp rfl
  have hlogpos : 1 ≤ Nat.log2 n := by
    by_cases hz : Nat.log2 n = 0
    · have hpown : 2^(Nat.log2 n+1) = 2 := by simp [hz]
      have hupper := hlog.2
      rw [hpown] at hupper
      omega
    · omega
  have hp : 2^((Nat.log2 n-1)+1) ≤ n := by
    have heq : (Nat.log2 n-1)+1=Nat.log2 n := by omega
    rw [heq]
    exact hlog.1
  have hh := prefix_superlinear f N (Nat.log2 n-1) n h hn hp
  have heq : (Nat.log2 n-1)+2=Nat.log2 n+1 := by omega
  rw [heq] at hh
  exact hh

#print axioms NeedleGrowth.prefix_log_growth
end NeedleGrowth
