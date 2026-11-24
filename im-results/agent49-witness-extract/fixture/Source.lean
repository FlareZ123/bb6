module
public import BusyBeaver.Basic
open BusyBeaver
@[expose] public section
def M : Machine Nat Nat := fun c => some {c with x := c.x+1}
def cfg (x : Nat) : Cfg Nat Nat := ⟨0,0,x⟩
end
macro "finish" : tactic => `(tactic| (refine ⟨0,?_⟩; rfl))
macro "step" : tactic => `(tactic| (
  try refine stepPlus_stepStar ?_
  apply step_stepStar_stepPlus (by rfl)))
macro "execute" n:num : tactic => `(tactic| (iterate $n step; finish))
private theorem t1 (x : Nat) : ReachesPlus M (cfg (0+x)) (cfg (x+3+0)) := by
  simp only [Nat.zero_add,Nat.add_zero]
  step
  step
  step
  finish
private theorem t2 (x : Nat) : ReachesPlus M (cfg (0+x)) (cfg (x+5+0)) := by
  rw [Nat.zero_add,Nat.add_zero]
  step
  step
  step
  step
  step
  finish
public theorem t1Pub (x : Nat) : ReachesPlus M (cfg (0+x)) (cfg (x+3+0)) := t1 x
public theorem t2Pub (x : Nat) : ReachesPlus M (cfg (0+x)) (cfg (x+5+0)) := t2 x
public theorem combined (x : Nat) : ReachesStar M (cfg (0+x)) (cfg (x+8+0)) := by
  have h1 := stepPlus_stepStar (t1Pub x)
  have h2 := stepPlus_stepStar (t2Pub (x+3))
  simp only [Nat.zero_add,Nat.add_zero] at h1 h2 ⊢
  exact ReachesStar.trans h1 h2
private theorem cycle (k x : Nat) : ReachesStar M (cfg x) (cfg (x+3*k)) := by
  induction k generalizing x with
  | zero => exact ⟨0,rfl⟩
  | succ k ih =>
    have h1 := stepPlus_stepStar (t1Pub x)
    have h2 := ih (x+3)
    have hh : x+3+3*k = x+3*(k+1) := by omega
    rw [Nat.zero_add,Nat.add_zero] at h1
    rw [hh] at h2
    exact ReachesStar.trans h1 h2
public theorem cyclePub (k x : Nat) : ReachesStar M (cfg x) (cfg (x+3*k)) := cycle k x
public theorem twoCycle (k x : Nat) : ReachesStar M (cfg x) (cfg (x+6*k)) := by
  have h1 := cycle k x
  have h2 := cycle k (x+3*k)
  have hh : x+3*k+3*k=x+6*k := by omega
  rw [hh] at h2
  exact ReachesStar.trans h1 h2
