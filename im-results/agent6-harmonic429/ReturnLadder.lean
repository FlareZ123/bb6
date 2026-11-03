import BB429Rank
import Lean.Elab.Tactic.Omega

/-!
A non-first-branch affine return and its bounded arithmetic ladders for
Cryptids BB6 holdout #429. Imports Agent 5's standalone, source-transcribed
BB429Rank, rather than duplicating its first-branch / rank proofs.
No original upstream source import is asserted here.
-/
namespace BB429Ladder
open BB429

def rayU : Nat → Nat
 | 0 => 0
 | n+1 => 2 * rayU n + 3

def rayDemand : Nat → Nat
 | 0 => 0
 | n+1 => rayDemand n + rayU (n+1)

theorem ray_balance (n : Nat) : rayDemand n + 3*n = 2*rayU n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rayDemand, rayU]; omega

theorem ray_run (n W : Nat) (h : rayDemand n ≤ W) :
    run n (0,W) = some (rayU n, W-rayDemand n) := by
  induction n with
  | zero => simp [run,rayU,rayDemand]
  | succ n ih =>
    have hd : rayDemand n ≤ W := by simp only [rayDemand] at h; omega
    have hs : W-rayDemand n ≥ 2*rayU n+3 := by
      simp only [rayDemand,rayU] at h
      omega
    simp only [run, ih hd, Option.bind_some]
    simp only [next, ge_iff_le, if_pos hs,rayU,rayDemand]
    simp only [Nat.sub_sub,Nat.add_assoc]

theorem reset_odd_even (u w : Nat) (hw : w%2=0)
    (hlt : w<2*u) (hd : 3≤u-w/2) (hodd : (u-w/2)%2=1) :
    next (u,w) = some (0,2*u+w+10) := by
  unfold next
  have h1 : ¬w ≥ 2*u+3 := by omega
  have h2 : w ≠ 2*u+2 := by omega
  have h3 : w ≠ 2*u+1 := by omega
  have h4 : w ≠ 2*u := by omega
  simp [h1,h2,h3,h4,hw, show u-w/2 ≠ 1 by omega,
    show ¬(u-w/2)%2=0 by omega]

theorem run_succ_front (n : Nat) (s : State) :
    run (n+1) s = (next s).bind (run n) := by
  calc
    run (n+1) s = run (1+n) s := by congr 1; omega
    _ = (run 1 s).bind (run n) := BB429.run_add 1 n s
    _ = (next s).bind (run n) := rfl

/-- A full non-first reset followed by k first-branch steps. -/
theorem ray_reset_return (k w : Nat)
    (hw : w%2=0)
    (hlt : w<2*rayU k)
    (hd : 3≤rayU k-w/2)
    (hodd : (rayU k-w/2)%2=1) :
    run (k+1) (rayU k,w) = some (rayU k,w+3*k+10) := by
  have hr := reset_odd_even (rayU k) w hw hlt hd hodd
  have hdemand := ray_balance k
  have hbound : rayDemand k ≤ 2*rayU k+w+10 := by omega
  have hrun := ray_run k (2*rayU k+w+10) hbound
  have hsub : 2*rayU k+w+10-rayDemand k=w+3*k+10 := by omega
  rw [run_succ_front, hr]
  simpa only [Option.bind_some,hsub] using hrun

theorem rayU_odd (k : Nat) (hk : 1≤k) : rayU k%2=1 := by
  cases k with
  | zero => omega
  | succ n => simp [rayU]

theorem ray_delta_quad (k : Nat) (hk : k%4=2) :
    (3*k+10)%4=0 := by omega

/-- Bounded affine return loops for all k congruent 2 mod 4. -/
theorem ray_ladder (k n w : Nat) (hk : 1≤k) (hk4 : k%4=2)
    (hw4 : w%4=0) (hb : w+n*(3*k+10)+4≤2*rayU k) :
    run (n*(k+1)) (rayU k,w) =
      some (rayU k,w+n*(3*k+10)) := by
  have hu : rayU k%2=1 := rayU_odd k hk
  have hdelta : (3*k+10)%4=0 := ray_delta_quad k hk4
  induction n with
  | zero => simp [run]
  | succ n ih =>
    have hbn : w+n*(3*k+10)+4≤2*rayU k := by
      rw [Nat.succ_mul] at hb
      omega
    have hmid4 : (w+n*(3*k+10))%4=0 := by
      simp [Nat.add_mod,Nat.mul_mod,hw4,hdelta]
    have heven : (w+n*(3*k+10))%2=0 := by omega
    have hlt : w+n*(3*k+10)<2*rayU k := by omega
    have hd : 3≤rayU k-(w+n*(3*k+10))/2 := by omega
    have hodd : (rayU k-(w+n*(3*k+10))/2)%2=1 := by omega
    have hreturn := ray_reset_return k (w+n*(3*k+10)) heven hlt hd hodd
    rw [Nat.succ_mul,BB429.run_add,ih hbn]
    simp only [Option.bind_some,hreturn]
    have hadd : w+n*(3*k+10)+3*k+10 = w+(n+1)*(3*k+10) := by
      rw [Nat.succ_mul n (3*k+10)]
      omega
    exact congrArg (fun z : Nat => some (rayU k,z)) hadd

/-- Authentic source-matched initial J(0,0) accelerated prefix. -/
theorem root_to_189_48 : run 79 (0,0) = some (189,48) := by decide

theorem actual_eleven_ladder : run 77 (189,48)=some (189,356) := by
  have hU : rayU 6=189 := by decide
  have hb : 48+11*(3*6+10)+4≤2*rayU 6 := by decide
  have h := ray_ladder 6 11 48 (by decide) (by decide) (by decide) hb
  simpa [hU] using h

theorem root_to_189_356 : run 156 (0,0)=some (189,356) := by
  rw [show 156=79+77 by decide,BB429.run_add,root_to_189_48]
  exact actual_eleven_ladder

#print axioms ray_balance
#print axioms ray_run
#print axioms reset_odd_even
#print axioms ray_reset_return
#print axioms ray_ladder
#print axioms root_to_189_356
end BB429Ladder
