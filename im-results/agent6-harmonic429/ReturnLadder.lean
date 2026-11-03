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

namespace BB429OddExtension
open BB429 BB429Ladder

/-- Two non-first source transitions: odd-odd turn, then even-odd reset. -/
theorem odd_odd_two_step (u w : Nat) (hu : u%2=1) (hu3 : 3≤u)
    (hw : w%4=1) (hbound : 3*w≤2*u+1) :
    run 2 (u,w)=some (0,2*u+w+17) := by
  have hpar : w%2=1 := by omega
  have hlt : w<2*u := by omega
  have hd : 3≤u-w/2 := by omega
  have hodd : (u-w/2)%2=1 := by omega
  have hfirst : next (u,w)=some (u-w/2+3,2*w) := by
    unfold next
    have hh1 : ¬w ≥ 2*u+3 := by omega
    have hh2 : w ≠ 2*u+2 := by omega
    have hh3 : w ≠ 2*u+1 := by omega
    have hh4 : w ≠ 2*u := by omega
    simp [hh1,hh2,hh3,hh4,show w%2 ≠0 by omega,
      show u-w/2 ≠1 by omega,show u-w/2 ≠2 by omega,
      show ¬(u-w/2)%2=0 by omega]
  have hsecond : next (u-w/2+3,2*w)=some (0,2*(u-w/2+3)+2*w+10) := by
    apply reset_odd_even
    · omega
    · omega
    · omega
    · omega
  have hcalc : 2*(u-w/2+3)+2*w+10=2*u+w+17 := by omega
  change (run 1 (u,w)).bind next = _
  simp [run,hfirst,hsecond,hcalc]

theorem odd_ray_return (k w : Nat) (hk : 1≤k) (hw : w%4=1)
    (hbound : 3*w≤2*rayU k+1) :
    run (k+2) (rayU k,w) = some (rayU k,w+3*k+17) := by
  have hUodd : rayU k%2=1 := rayU_odd k hk
  have hU3 : 3≤rayU k := by cases k with
    | zero => omega
    | succ n => simp [rayU]
  have htwo := odd_odd_two_step (rayU k) w hUodd hU3 hw hbound
  have hbal := ray_balance k
  have hbd : rayDemand k≤2*rayU k+w+17 := by omega
  have hray := ray_run k (2*rayU k+w+17) hbd
  have hsub : 2*rayU k+w+17-rayDemand k=w+3*k+17 := by omega
  rw [show k+2=2+k by omega,BB429.run_add,htwo]
  simpa only [Option.bind_some,hsub] using hray

/-- Additional family: k=1 mod 4, w=1 mod 4 and an odd-odd entry. -/
theorem odd_ray_ladder (k n w : Nat) (hk : 1≤k) (hk4 : k%4=1)
    (hw4 : w%4=1) (hb : 3*(w+n*(3*k+17))≤2*rayU k+1) :
    run (n*(k+2)) (rayU k,w) = some (rayU k,w+n*(3*k+17)) := by
  have hdelta : (3*k+17)%4=0 := by omega
  induction n with
  | zero => simp [run]
  | succ n ih =>
    have hbn : 3*(w+n*(3*k+17))≤2*rayU k+1 := by
      rw [Nat.succ_mul n (3*k+17)] at hb
      omega
    have hw4n : (w+n*(3*k+17))%4=1 := by
      simp [Nat.add_mod,Nat.mul_mod,hw4,hdelta]
    have hreturn := odd_ray_return k (w+n*(3*k+17)) hk hw4n hbn
    rw [Nat.succ_mul,BB429.run_add,ih hbn]
    simp only [Option.bind_some,hreturn]
    have heq : w+n*(3*k+17)+3*k+17 = w+(n+1)*(3*k+17) := by
      rw [Nat.succ_mul n (3*k+17)]
      omega
    exact congrArg (fun z : Nat => some (rayU k,z)) heq

theorem rooted_odd_ladder_entry : run 33 (0,0)=some (93,13) := by decide

theorem rooted_odd_ladder_exit : run 40 (0,0)=some (93,45) := by
  have hk : rayU 5=93 := by decide
  have hb : 3*(13+1*(3*5+17))≤2*rayU 5+1 := by decide
  have hx := odd_ray_ladder 5 1 13 (by decide) (by decide) (by decide) hb
  rw [show 40=33+7 by decide,BB429.run_add,rooted_odd_ladder_entry]
  simpa [hk] using hx

#print axioms odd_odd_two_step
#print axioms odd_ray_return
#print axioms odd_ray_ladder
#print axioms rooted_odd_ladder_exit
end BB429OddExtension

namespace BB429ElevenExtension
open BB429 BB429Ladder

/-- Exact doubling ray after a reset into first counter 11. -/
def rayV : Nat → Nat
 | 0 => 11
 | k+1 => 2*rayV k+3

def demandV : Nat → Nat
 | 0 => 0
 | k+1 => demandV k+rayV (k+1)

theorem v_balance (k : Nat) : demandV k+3*k+22=2*rayV k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [demandV,rayV]; omega

theorem v_run (k W : Nat) (h : demandV k≤W) :
    run k (11,W)=some (rayV k,W-demandV k) := by
  induction k with
  | zero => simp [run,rayV,demandV]
  | succ k ih =>
    have hk : demandV k≤W := by simp only [demandV] at h; omega
    have hg : W-demandV k ≥ 2*rayV k+3 := by
      simp only [demandV,rayV] at h
      omega
    simp only [run,ih hk,Option.bind_some]
    simp only [next, ge_iff_le, if_pos hg,rayV,demandV]
    simp only [Nat.sub_sub,Nat.add_assoc]

theorem vU_odd (k:Nat):rayV k%2=1 := by
  cases k with
  | zero => decide
  | succ k => simp [rayV]

theorem vU_large (k:Nat):11≤rayV k := by
  induction k with
  | zero => decide
  | succ k ih => simp only [rayV]; omega

theorem reset_even2 (u w:Nat)(hu:u%2=1)(hw:w%4=2)
    (hbound:w+4≤2*u):next (u,w)=some (11,2*u+w-2) := by
  have hlt:w<2*u:=by omega
  have hd:2≤u-w/2:=by omega
  have heven:w%2=0:=by omega
  have hdeven:(u-w/2)%2=0:=by omega
  unfold next
  have h1:¬w≥2*u+3:=by omega
  have h2:w≠2*u+2:=by omega
  have h3:w≠2*u+1:=by omega
  have h4:w≠2*u:=by omega
  simp [h1,h2,h3,h4,heven,show u-w/2 ≠1 by omega,hdeven]

theorem v_even_return (k w:Nat)(hw:w%4=2)(hb:w+4≤2*rayV k):
    run (k+1) (rayV k,w)=some (rayV k,w+3*k+20) := by
  have hreset:=reset_even2 (rayV k) w (vU_odd k) hw hb
  have hbal:=v_balance k
  have hd:demandV k≤2*rayV k+w-2:=by omega
  have hv:=v_run k (2*rayV k+w-2) hd
  have hsub:2*rayV k+w-2-demandV k=w+3*k+20:=by omega
  rw [run_succ_front,hreset]
  simpa only [Option.bind_some,hsub] using hv

theorem v_even_ladder (k n w:Nat)(hk4:k%4=0)(hw4:w%4=2)
    (hb:w+n*(3*k+20)+4≤2*rayV k):
    run (n*(k+1)) (rayV k,w)=some (rayV k,w+n*(3*k+20)) := by
  have hdelta:(3*k+20)%4=0:=by omega
  induction n with
  | zero => simp [run]
  | succ n ih =>
    have hbn:w+n*(3*k+20)+4≤2*rayV k:=by
      rw [Nat.succ_mul n (3*k+20)] at hb
      omega
    have hw4n:(w+n*(3*k+20))%4=2:=by
      simp [Nat.add_mod,Nat.mul_mod,hw4,hdelta]
    have hret:=v_even_return k (w+n*(3*k+20)) hw4n hbn
    rw [Nat.succ_mul,BB429.run_add,ih hbn]
    simp only [Option.bind_some,hret]
    have heq:w+n*(3*k+20)+3*k+20=w+(n+1)*(3*k+20):=by
      rw [Nat.succ_mul n (3*k+20)]
      omega
    exact congrArg (fun z:Nat=>some (rayV k,z)) heq

#print axioms v_even_return
#print axioms v_even_ladder
end BB429ElevenExtension

namespace BB429ElevenOddExtension
open BB429 BB429Ladder BB429ElevenExtension

/-- Two non-first resets, into first counter 11. -/
theorem odd_even_two_step (u w:Nat) (hu:u%2=1)(hu11:11≤u)
    (hw:w%4=3)(hb:3*w≤2*u+15):
    run 2 (u,w)=some (11,2*u+w+9) := by
  have hwodd:w%2=1:=by omega
  have hw3:3≤w:=by omega
  have hlt:w<2*u:=by omega
  have hd:4≤u-w/2:=by omega
  have hdeven:(u-w/2)%2=0:=by omega
  have hfirst:next (u,w)=some (u-w/2+7,2*w-4) := by
    unfold next
    have h1:¬w≥2*u+3:=by omega
    have h2:w≠2*u+2:=by omega
    have h3:w≠2*u+1:=by omega
    have h4:w≠2*u:=by omega
    simp [h1,h2,h3,h4,show w%2≠0 by omega,
      show u-w/2≠1 by omega,show u-w/2≠2 by omega,
      hdeven,show w≠1 by omega]
  have hsecond:next (u-w/2+7,2*w-4)=
      some (11,2*(u-w/2+7)+(2*w-4)-2) := by
    apply reset_even2
    · omega
    · omega
    · omega
  have hcalc:2*(u-w/2+7)+(2*w-4)-2=2*u+w+9:=by omega
  change (run 1 (u,w)).bind next=_
  simp [run,hfirst,hsecond,hcalc]

theorem v_odd_return (k w:Nat)(hw:w%4=3)(hb:3*w≤2*rayV k+15):
    run (k+2) (rayV k,w)=some (rayV k,w+3*k+31) := by
  have htwo:=odd_even_two_step (rayV k) w (vU_odd k) (vU_large k) hw hb
  have hbal:=v_balance k
  have hbd:demandV k≤2*rayV k+w+9:=by omega
  have hray:=v_run k (2*rayV k+w+9) hbd
  have hsub:2*rayV k+w+9-demandV k=w+3*k+31:=by omega
  rw [show k+2=2+k by omega,BB429.run_add,htwo]
  simpa only [Option.bind_some,hsub] using hray

theorem v_odd_ladder (k n w:Nat)(hk4:k%4=3)(hw4:w%4=3)
    (hb:3*(w+n*(3*k+31))≤2*rayV k+15):
    run (n*(k+2)) (rayV k,w)=some (rayV k,w+n*(3*k+31)) := by
  have hdelta:(3*k+31)%4=0:=by omega
  induction n with
  | zero=>simp [run]
  | succ n ih=>
    have hbn:3*(w+n*(3*k+31))≤2*rayV k+15:=by
      rw [Nat.succ_mul n (3*k+31)] at hb
      omega
    have hw4n:(w+n*(3*k+31))%4=3:=by
      simp [Nat.add_mod,Nat.mul_mod,hw4,hdelta]
    have hret:=v_odd_return k (w+n*(3*k+31)) hw4n hbn
    rw [Nat.succ_mul,BB429.run_add,ih hbn]
    simp only [Option.bind_some,hret]
    have heq:w+n*(3*k+31)+3*k+31=w+(n+1)*(3*k+31):=by
      rw [Nat.succ_mul n (3*k+31)]
      omega
    exact congrArg (fun z:Nat=>some (rayV k,z)) heq

#print axioms odd_even_two_step
#print axioms v_odd_return
#print axioms v_odd_ladder
end BB429ElevenOddExtension
