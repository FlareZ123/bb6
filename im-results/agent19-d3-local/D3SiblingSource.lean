import D3SiblingInvariant
import SweepPumping
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6Coverage.Agent31Pump.D3RE
open BB6Coverage Agent31Pump Agent50Zipper

/-- The exact canonical Raw13 D1=0RE child. F1 is the sole hole. -/
def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,2⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨true,true,4⟩)
  | 2,false => some (some ⟨true,false,0⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨false,true,1⟩)
  | 3,true => some (some ⟨false,true,4⟩)
  | 4,false => some (some ⟨true,true,1⟩)
  | 4,true => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | 5,true => none
  | _,_ => none

/-- Reflect the tape and relabel canonical A,B,C,D,E,F to B,C,A,E,D,F.
    The zipper left list includes the scanned cell, so mapping FROM it
    into Boundary avoids an explicit-zero padding side condition. -/
def orient (q : Fin 6) : Nat :=
  match q.val with
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 4
  | 4 => 3
  | _ => 5

def source (z : Z0) : D3SiblingBoundary.Cfg :=
  ⟨z.r,z.l.headD false,z.l.tail,orient z.q⟩

theorem step_transport (z : Z0) :
    match step0 p z with
    | none => (D3SiblingBoundary.step (source z)).st = 6
    | some t => D3SiblingBoundary.step (source z) = source t := by
  rcases z with ⟨q,l,r⟩
  have hq := (by decide : ∀ q : Fin 6, q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5) q
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;>
    cases l with
    | nil => cases r <;> rfl
    | cons a l => cases a <;> cases l <;> cases r <;> rfl

theorem run0_live (n : Nat) (z : Z0)
    (h : ∀ k, (D3SiblingBoundary.run k (source z)).st ≠ 6) :
    ∃ t, run0 p n z = some t := by
  induction n generalizing z with
  | zero => exact ⟨z,rfl⟩
  | succ n ih =>
    have H := step_transport z
    cases he : step0 p z with
    | none =>
      rw [he] at H
      exact False.elim (h 1 H)
    | some t =>
      rw [he] at H
      have ht : ∀ k, (D3SiblingBoundary.run k (source t)).st ≠ 6 := by
        intro k
        have hh := h (1+k)
        rw [D3SiblingBoundary.run_add] at hh
        change (D3SiblingBoundary.run k (D3SiblingBoundary.step (source z))).st ≠ 6 at hh
        rwa [H] at hh
      obtain ⟨w,hw⟩ := ih t ht
      exact ⟨w,by simp [run0,he,hw]⟩

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  intro n
  obtain ⟨z,hz⟩ := run0_live n ⟨0,[],[]⟩ D3SiblingBoundary.bblank_never
  have h := (run_project p n start).trans hz
  cases he : zrun p n start with
  | none => simp [he] at h
  | some t =>
    have H := zrun_sound p m hm n start t he
    rw [start_embed] at H
    rw [H]
    rfl

#print axioms step_transport
#print axioms run0_live
#print axioms never
end BB6Coverage.Agent31Pump.D3RE
