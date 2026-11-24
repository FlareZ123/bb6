import BlockPump

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent2Raw99
open BB6Coverage BB6Coverage.Agent50Zipper BB6Coverage.Agent50Pump

theorem getD_append_false (l : List Bool) (n : Nat) :
    (l ++ [false]).getD n false = l.getD n false := by
  induction l generalizing n with
  | nil => cases n <;> rfl
  | cons b l ih => cases n with
    | zero => rfl
    | succ n => simpa only [List.cons_append, List.getD_cons_succ] using ih n

def padHZ (z : HZ) : HZ := {z with l := z.l ++ [false]}

theorem pad_embed (z : HZ) (h : Int) :
    embed ((padHZ z).at h) = embed (z.at h) := by
  unfold HZ.at embed
  congr 1
  funext x
  simp [atCell, padHZ, getD_append_false]

def padShape (s : Shape) : Shape :=
  {s with l := {s.l with post := s.l.post ++ [false]}}

theorem pad_eval (s : Shape) (n : Nat) :
    (padShape s).eval n = padHZ (s.eval n) := by
  simp [padShape, padHZ, Shape.eval, Word.eval, List.append_assoc]

def padCheck (p : PartialMachine) (c : Certificate) : Bool :=
  decide (hrun p c.entry ⟨0,[],[]⟩ = some (c.shape.eval 0)) &&
  decide (runOps p c.ops c.shape = some (padShape c.shape.grow)) &&
  decide (0 < lower c.ops)

/-- A single outer false cell is immaterial to the physical tape.
    The induction runs over actual source configurations, so it does not
    require an equality between two differently padded zipper lists. -/
theorem padNever (p : PartialMachine) (c : Certificate)
    (h : padCheck p c = true) (m : Machine) (hm : compatible p m) :
    NeverHalts m := by
  simp [padCheck] at h
  have arbitrary : ∀ n : Nat, ∃ k : Nat, ∃ x : Int,
      n ≤ k ∧ run m k blank = some (embed ((c.shape.eval n).at x)) := by
    intro n
    induction n with
    | zero =>
      obtain ⟨x, hx⟩ := hrun_sound p c.entry _ _ 0 h.1.1
      have hr := zrun_sound p m hm c.entry _ _ hx
      rw [blank_embed] at hr
      exact ⟨c.entry,x,by omega,hr⟩
    | succ n ih =>
      obtain ⟨k,x,hk,hx⟩ := ih
      obtain ⟨t,ht,Ht⟩ := runOps_sound p c.ops c.shape (padShape c.shape.grow) h.1.2 n
      obtain ⟨y,hy⟩ := hrun_sound p t _ _ x Ht
      have hr := zrun_sound p m hm t _ _ hy
      rw [pad_eval, Shape.grow_sound, pad_embed] at hr
      refine ⟨k+t,y,by omega,?_⟩
      rw [run_append,hx]
      exact hr
  intro n
  obtain ⟨k,x,hk,Hk⟩ := arbitrary n
  rw [show k = n+(k-n) by omega,run_append] at Hk
  cases he : run m n blank with
  | none => simp [he] at Hk
  | some z => rfl

#print axioms padNever
end BB6.Agent2Raw99
