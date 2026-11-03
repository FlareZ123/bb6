import BusyBeaver.BB6.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA
import OddVHigh
import Lean.Elab.Tactic.Omega

/-!
Native-source semantic bridge for BB429Ladder. This compares each source
highLevelNext transition with Agent5's standalone BB429.next, then transports
all accelerated iterates and the new non-first-branch affine ladder.
-/
namespace BB429SourceLadder
open BusyBeaver.M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA

def lift (s : BB429.State) : HighLevelState := .J s.1 s.2

set_option maxHeartbeats 5000000 in
theorem source_step_eq (u w : Nat) :
    highLevelNext (.J u w) = (BB429.next (u,w)).map lift := by
  simp only [highLevelNext, BB429.next]
  all_goals (first | rfl | (split <;> try simp_all [lift]))
  all_goals (first | rfl | (split <;> try simp_all [lift]))
  all_goals (first | rfl | (split <;> try simp_all [lift]))
  all_goals (first | rfl | (split <;> try simp_all [lift]))
  all_goals (first | rfl | (split <;> try simp_all [lift]))
  all_goals (first | rfl | (split <;> try simp_all [lift]))
  all_goals (first | rfl | (split <;> try simp_all [lift]))
  all_goals (first | rfl | (split <;> try simp_all [lift]))
  all_goals (first | rfl | (split <;> try simp_all [lift]))
  all_goals (first | rfl | (split <;> try simp_all [lift]))
  all_goals (first | rfl | (split <;> try simp_all [lift]))
  all_goals (first | rfl | (split <;> try simp_all [lift]))
  all_goals (first | rfl | (split <;> try simp_all [lift]))
  all_goals (first | rfl | (split <;> try simp_all [lift]))

def sourceRun : Nat → HighLevelState → Option HighLevelState
 | 0,s => some s
 | n+1,s => (sourceRun n s).bind highLevelNext

theorem source_run_eq (n : Nat) (s : BB429.State) :
    sourceRun n (lift s) = (BB429.run n s).map lift := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sourceRun, BB429.run, ih]
    cases hr : BB429.run n s with
    | none => simp [hr]
    | some t =>
      cases t with
      | mk u w =>
        simpa only [hr, Option.map_some, Option.bind_some, lift] using
          (source_step_eq u w)

/-- A source-connected, quantified non-first-branch return theorem. -/
theorem source_ray_ladder (k n w : Nat) (hk : 1≤k) (hk4 : k%4=2)
    (hw4 : w%4=0)
    (hb : w+n*(3*k+10)+4≤2*BB429Ladder.rayU k) :
    sourceRun (n*(k+1)) (.J (BB429Ladder.rayU k) w) =
      some (.J (BB429Ladder.rayU k) (w+n*(3*k+10))) := by
  have h := BB429Ladder.ray_ladder k n w hk hk4 hw4 hb
  have hh := source_run_eq (n*(k+1)) (BB429Ladder.rayU k,w)
  simpa [lift,h] using hh

theorem source_root_to_189_356 :
    sourceRun 156 highLevelStart = some (.J 189 356) := by
  have hh := source_run_eq 156 (0,0)
  simpa [lift,highLevelStart,BB429Ladder.root_to_189_356] using hh

/-- Second source-connected family: two resets and k first-branch moves. -/
theorem source_odd_ray_ladder (k n w : Nat) (hk : 1≤k) (hk4 : k%4=1)
    (hw4 : w%4=1)
    (hb : 3*(w+n*(3*k+17))≤2*BB429Ladder.rayU k+1) :
    sourceRun (n*(k+2)) (.J (BB429Ladder.rayU k) w) =
      some (.J (BB429Ladder.rayU k) (w+n*(3*k+17))) := by
  have h := BB429OddExtension.odd_ray_ladder k n w hk hk4 hw4 hb
  have hh := source_run_eq (n*(k+2)) (BB429Ladder.rayU k,w)
  simpa [lift,h] using hh

theorem source_root_to_93_45 :
    sourceRun 40 highLevelStart = some (.J 93 45) := by
  have hh := source_run_eq 40 (0,0)
  simpa [lift,highLevelStart,BB429OddExtension.rooted_odd_ladder_exit] using hh

#print axioms source_odd_ray_ladder
#print axioms source_root_to_93_45

/-- Third affine ladder family on the ray from state 11, even return. -/
theorem source_v_even_ladder (k n w : Nat) (hk4 : k%4=0) (hw4 : w%4=2)
    (hb : w+n*(3*k+20)+4≤2*BB429ElevenExtension.rayV k) :
    sourceRun (n*(k+1)) (.J (BB429ElevenExtension.rayV k) w) =
      some (.J (BB429ElevenExtension.rayV k) (w+n*(3*k+20))) := by
  have h := BB429ElevenExtension.v_even_ladder k n w hk4 hw4 hb
  have hh := source_run_eq (n*(k+1)) (BB429ElevenExtension.rayV k,w)
  simpa [lift,h] using hh

/-- Fourth affine ladder family on the ray from state 11, odd return. -/
theorem source_v_odd_ladder (k n w : Nat) (hk4 : k%4=3) (hw4 : w%4=3)
    (hb : 3*(w+n*(3*k+31))≤2*BB429ElevenExtension.rayV k+15) :
    sourceRun (n*(k+2)) (.J (BB429ElevenExtension.rayV k) w) =
      some (.J (BB429ElevenExtension.rayV k) (w+n*(3*k+31))) := by
  have h := BB429ElevenOddExtension.v_odd_ladder k n w hk4 hw4 hb
  have hh := source_run_eq (n*(k+2)) (BB429ElevenExtension.rayV k,w)
  simpa [lift,h] using hh

#print axioms source_v_even_ladder
#print axioms source_v_odd_ladder

/-- Native Cryptids exact accelerated source checkpoint from the true blank-origin state. -/
theorem source_root_to_V5_745 :
    sourceRun 322 highLevelStart =
      some (.J (BB429ElevenExtension.rayV 5) 745) := by
  have hh:=source_run_eq 322 (0,0)
  simpa [lift,highLevelStart,BB429OddVHigh.rooted_to_V5_745] using hh

#print axioms source_root_to_V5_745

#print axioms source_step_eq
#print axioms source_run_eq
#print axioms source_ray_ladder
#print axioms source_root_to_189_356
end BB429SourceLadder
