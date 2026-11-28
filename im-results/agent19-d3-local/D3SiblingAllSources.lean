import D3SiblingAllStarts
import SweepPumping

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent31Pump.D3Variant
open BB6Coverage Agent31Pump Agent50Zipper

/-- A start-state indexed family with first-use state names and rightward
    initial motion. Start 4 starts with a zero write, so is not a TNF
    initial-1 representative; the direct nonhalting theorem still applies. -/
def p (s : Fin 6) : PartialMachine := fun slot =>
  match s.val,slot.1.val,slot.2 with
  | 0,0,false => some (some ⟨true,true,1⟩)
  | 0,0,true => some (some ⟨false,true,4⟩)
  | 0,1,false => some (some ⟨true,false,2⟩)
  | 0,1,true => some (some ⟨false,true,0⟩)
  | 0,2,false => some (some ⟨true,false,0⟩)
  | 0,2,true => some (some ⟨true,false,3⟩)
  | 0,3,false => some (some ⟨true,false,2⟩)
  | 0,3,true => some (some ⟨true,false,5⟩)
  | 0,4,false => some (some ⟨false,false,2⟩)
  | 0,4,true => some (some ⟨false,false,3⟩)
  | 0,5,false => some (some ⟨true,false,4⟩)
  | 1,0,false => some (some ⟨true,true,1⟩)
  | 1,0,true => some (some ⟨false,false,2⟩)
  | 1,1,false => some (some ⟨true,true,2⟩)
  | 1,1,true => some (some ⟨true,true,4⟩)
  | 1,2,false => some (some ⟨true,false,0⟩)
  | 1,2,true => some (some ⟨false,false,3⟩)
  | 1,3,false => some (some ⟨false,true,1⟩)
  | 1,3,true => some (some ⟨false,true,4⟩)
  | 1,4,false => some (some ⟨true,true,1⟩)
  | 1,4,true => some (some ⟨true,true,5⟩)
  | 1,5,false => some (some ⟨true,true,3⟩)
  | 2,0,false => some (some ⟨true,true,1⟩)
  | 2,0,true => some (some ⟨true,true,3⟩)
  | 2,1,false => some (some ⟨true,false,2⟩)
  | 2,1,true => some (some ⟨false,false,4⟩)
  | 2,2,false => some (some ⟨true,true,0⟩)
  | 2,2,true => some (some ⟨false,false,1⟩)
  | 2,3,false => some (some ⟨true,true,0⟩)
  | 2,3,true => some (some ⟨true,true,5⟩)
  | 2,4,false => some (some ⟨false,true,0⟩)
  | 2,4,true => some (some ⟨false,true,3⟩)
  | 2,5,false => some (some ⟨true,true,4⟩)
  | 3,0,false => some (some ⟨true,true,1⟩)
  | 3,0,true => some (some ⟨true,true,5⟩)
  | 3,1,false => some (some ⟨true,true,2⟩)
  | 3,1,true => some (some ⟨true,true,0⟩)
  | 3,2,false => some (some ⟨true,false,3⟩)
  | 3,2,true => some (some ⟨false,false,4⟩)
  | 3,3,false => some (some ⟨true,true,1⟩)
  | 3,3,true => some (some ⟨false,false,2⟩)
  | 3,4,false => some (some ⟨false,true,1⟩)
  | 3,4,true => some (some ⟨false,true,0⟩)
  | 3,5,false => some (some ⟨true,true,4⟩)
  | 4,0,false => some (some ⟨false,true,1⟩)
  | 4,0,true => some (some ⟨false,true,4⟩)
  | 4,1,false => some (some ⟨true,true,2⟩)
  | 4,1,true => some (some ⟨true,true,4⟩)
  | 4,2,false => some (some ⟨true,false,3⟩)
  | 4,2,true => some (some ⟨false,false,0⟩)
  | 4,3,false => some (some ⟨true,true,1⟩)
  | 4,3,true => some (some ⟨false,false,2⟩)
  | 4,4,false => some (some ⟨true,true,1⟩)
  | 4,4,true => some (some ⟨true,true,5⟩)
  | 4,5,false => some (some ⟨true,true,0⟩)
  | 5,0,false => some (some ⟨true,true,1⟩)
  | 5,1,false => some (some ⟨false,true,2⟩)
  | 5,1,true => some (some ⟨false,true,5⟩)
  | 5,2,false => some (some ⟨true,true,3⟩)
  | 5,2,true => some (some ⟨true,true,5⟩)
  | 5,3,false => some (some ⟨true,false,4⟩)
  | 5,3,true => some (some ⟨false,false,1⟩)
  | 5,4,false => some (some ⟨true,true,2⟩)
  | 5,4,true => some (some ⟨false,false,3⟩)
  | 5,5,false => some (some ⟨true,true,2⟩)
  | 5,5,true => some (some ⟨true,true,0⟩)
  | _,_,_ => none

def orient (s q : Fin 6) : Fin 6 :=
  match s.val,q.val with
  | 0,0 => 0
  | 0,1 => 1
  | 0,2 => 2
  | 0,3 => 3
  | 0,4 => 4
  | 0,5 => 5
  | 1,0 => 1
  | 1,1 => 2
  | 1,2 => 0
  | 1,3 => 4
  | 1,4 => 3
  | 1,5 => 5
  | 2,0 => 2
  | 2,1 => 0
  | 2,2 => 1
  | 2,3 => 3
  | 2,4 => 4
  | 2,5 => 5
  | 3,0 => 3
  | 3,1 => 2
  | 3,2 => 0
  | 3,3 => 1
  | 3,4 => 4
  | 3,5 => 5
  | 4,0 => 4
  | 4,1 => 2
  | 4,2 => 0
  | 4,3 => 1
  | 4,4 => 3
  | 4,5 => 5
  | 5,0 => 5
  | 5,1 => 4
  | 5,2 => 2
  | 5,3 => 0
  | 5,4 => 1
  | 5,5 => 3
  | _,_ => 0

def source (s : Fin 6) (z : Z0) : D3SiblingBoundary.Cfg :=
  if s = 0 then ⟨z.l.tail,z.l.headD false,z.r,(orient s z.q).val⟩
  else ⟨z.r,z.l.headD false,z.l.tail,(orient s z.q).val⟩

theorem fin_cases (q : Fin 6) : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 :=
  (by decide : ∀ q : Fin 6, q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5) q

theorem step_transport (s : Fin 6) (z : Z0) :
    match step0 (p s) z with
    | none => (D3SiblingBoundary.step (source s z)).st = 6
    | some t => D3SiblingBoundary.step (source s z) = source s t := by
  rcases z with ⟨q,l,r⟩
  rcases fin_cases s with rfl|rfl|rfl|rfl|rfl|rfl <;>
    rcases fin_cases q with rfl|rfl|rfl|rfl|rfl|rfl <;>
    cases l with
    | nil => cases r <;> rfl
    | cons a l => cases a <;> cases l <;> cases r <;> rfl

theorem run0_live (s : Fin 6) (n : Nat) (z : Z0)
    (h : ∀ k, (D3SiblingBoundary.run k (source s z)).st ≠ 6) :
    ∃ t, run0 (p s) n z = some t := by
  induction n generalizing z with
  | zero => exact ⟨z,rfl⟩
  | succ n ih =>
    have H := step_transport s z
    cases he : step0 (p s) z with
    | none =>
      rw [he] at H
      exact False.elim (h 1 H)
    | some t =>
      rw [he] at H
      have ht : ∀ k, (D3SiblingBoundary.run k (source s t)).st ≠ 6 := by
        intro k
        have hh := h (1+k)
        rw [D3SiblingBoundary.run_add] at hh
        change (D3SiblingBoundary.run k (D3SiblingBoundary.step (source s z))).st ≠ 6 at hh
        rwa [H] at hh
      obtain ⟨w,hw⟩ := ih t ht
      exact ⟨w,by simp [run0,he,hw]⟩

theorem source_blank (s : Fin 6) : source s ⟨0,[],[]⟩ = D3SiblingBoundary.blankAt s := by
  rcases fin_cases s with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem never (s : Fin 6) (m : Machine) (hm : compatible (p s) m) : NeverHalts m := by
  intro n
  have hb : ∀ k, (D3SiblingBoundary.run k (source s ⟨0,[],[]⟩)).st ≠ 6 := by
    rw [source_blank]
    exact D3SiblingBoundary.blankAt_never s
  obtain ⟨z,hz⟩ := run0_live s n ⟨0,[],[]⟩ hb
  have h := (run_project (p s) n start).trans hz
  cases he : zrun (p s) n start with
  | none => simp [he] at h
  | some t =>
    have H := zrun_sound (p s) m hm n start t he
    rw [start_embed] at H
    rw [H]
    rfl

#print axioms step_transport
#print axioms never
end BB6Coverage.Agent31Pump.D3Variant
