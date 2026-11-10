import NeedleTwoStep
import NeedleGrowthFinite
import Lean.Elab.Tactic.Omega

namespace NeedleGrowth
private theorem edge_pos {b c : Nat} (h : Edge b c) : b<c := by
  rcases h with ⟨q,v,_,hc⟩
  omega

private theorem square_next (m : Nat) :
    (m+2)^2+1 ≤ (m+1)^2+1+2*(m+2) := by
  simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul]
  omega

theorem two_step_ge_square (f : Nat → Nat) (N i k : Nat)
    (h : Prefix f N) (hi : i+2≤N)
    (hk : (k+1)^2 < f i) :
    f i+(k+2) ≤ f (i+2) := by
  have h0 := h i (by omega)
  have h1 := h (i+1) (by omega)
  have hle0 := edge_pos h0
  have hle1 := edge_pos h1
  have hsq := two_step_square_gain h0 h1
  have hidx : i+1+1=i+2 := by omega
  rw [hidx] at hsq
  have hdelta : k+2 ≤ f (i+2)-f i := by
    by_cases hsmall : f (i+2)-f i ≤ k+1
    · have hmul := Nat.mul_le_mul hsmall hsmall
      have hpow : (f (i+2)-f i)^2 ≤ (k+1)^2 := by
        simpa [Nat.pow_succ] using hmul
      omega
    · omega
  omega

/-- Quadratic growth through four-step blocks of every successful prefix. -/
theorem prefix_quadratic (f : Nat → Nat) (N m : Nat)
    (h : Prefix f N) (hbase : 2 ≤ f 0) (hm : 4*m ≤ N) :
    (m+1)^2+1 ≤ f (4*m) := by
  induction m with
  | zero => simpa using hbase
  | succ m ih =>
      have hprev : 4*m ≤ N := by omega
      have hb := ih hprev
      have h0 := two_step_ge_square f N (4*m) m h (by omega) (by omega)
      have hlow : (m+1)^2 < f (4*m+2) := by omega
      have h1 := two_step_ge_square f N (4*m+2) m h (by omega) hlow
      have hsq := square_next m
      have heq : 4*(m+1) = (4*m+2)+2 := by omega
      rw [heq]
      have hmnext : m+1+1=m+2 := by omega
      rw [hmnext]
      omega

private theorem prefix_monotone (f : Nat → Nat) (N i t : Nat)
    (h : Prefix f N) (ht : i+t≤N) : f i ≤ f (i+t) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hpre : i+t ≤ N := by omega
      have hb := ih hpre
      have hs := edge_pos (h (i+t) (by omega))
      have heq : i+(t+1)=i+t+1 := by omega
      rw [heq]
      omega

/-- Complete quadratic lower bound for each finite successful prefix. -/
theorem prefix_quadratic_index (f : Nat → Nat) (N n : Nat)
    (h : Prefix f N) (hbase : 2 ≤ f 0) (hn : n ≤ N) :
    (n/4+1)^2+1 ≤ f n := by
  have h4 : 4*(n/4) ≤ n := Nat.mul_div_le n 4
  have hquad := prefix_quadratic f N (n/4) h hbase (by omega)
  have hlin := prefix_linear f N h n hn
  have hmon : f (4*(n/4)) ≤ f n := by
    have hseg := prefix_monotone f N (4*(n/4)) (n-4*(n/4)) h (by omega)
    have heq : 4*(n/4)+(n-4*(n/4))=n := by omega
    rwa [heq] at hseg
  omega

/-- An exact natural-square-root upper bound on return time. -/
theorem quadratic_index_sqrt_bound (d n : Nat)
    (h : (n/4+1)^2+1 ≤ d+2) :
    n < 4*(Nat.sqrt (d+1)+1) := by
  have hsq : (n/4+1)*(n/4+1) ≤ d+1 := by
    have hmain : (n/4+1)^2 ≤ d+1 := by omega
    simpa [Nat.pow_succ] using hmain
  have hk : n/4+1 ≤ Nat.sqrt (d+1) := by
    by_cases hbig : Nat.sqrt (d+1)+1 ≤ n/4+1
    · have hmul := Nat.mul_le_mul hbig hbig
      have heq : Nat.sqrt (d+1)+1 = (Nat.sqrt (d+1)).succ := by omega
      rw [heq] at hmul
      have hlt := Nat.lt_succ_sqrt (d+1)
      omega
    · omega
  have hnlt : n < (n/4+1)*4 :=
    (Nat.div_lt_iff_lt_mul (by omega)).mp (by omega : n/4 < n/4+1)
  have hmul := Nat.mul_le_mul_right 4 hk
  omega

#print axioms NeedleGrowth.two_step_ge_square
#print axioms NeedleGrowth.prefix_quadratic
#print axioms NeedleGrowth.prefix_quadratic_index
#print axioms NeedleGrowth.quadratic_index_sqrt_bound
end NeedleGrowth
