import CapMulti
import BusyBeaver.BB6.M_1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_HHH0LE
import BusyBeaver.BB6.M_1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_HHH0RE
import BusyBeaver.BB6.M_1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_HHH0RE

open BusyBeaver
namespace CapSource

theorem runs_to_steps {S : Type} {step : S → Option S} {s : S} {r : Option S}
    (h : Cap.RunsTo step s r) : CollatzStepsTo step s r := by
  induction h with
  | one s => exact CollatzStepsTo.of_eq rfl
  | head e _ ih => exact CollatzStepsTo.head e ih

theorem halt_runs {S : Type} {step : S → Option S} {s : S}
    (h : CollatzHalts step s) : Cap.RunsTo step s none := by
  obtain ⟨n,hn⟩ := h
  induction n generalizing s with
  | zero => simp at hn
  | succ n ih =>
    rw [Function.iterate_succ_apply] at hn
    cases e : step s with
    | none => exact Cap.RunsTo.of_eq e
    | some t => exact .head e (ih (by simpa [e] using hn))

theorem section_halts_iff (n : Nat) : CollatzHalts Cap.sectionNext n ↔ Cap.haltsAtRoot (n+2) := by
  rw [←Cap.section_halts]
  exact ⟨halt_runs, runs_to_steps⟩

namespace H421
open BusyBeaver.M_1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_HHH0LE

theorem eval_copy (b c : Nat) : evalD0 b c = (Cap.eval b c).map HighLevelState.C := by
  induction b using Nat.strongRecOn generalizing c with
  | ind b ih =>
    rw [evalD0,Cap.eval]
    split
    · split
      · rfl
      · split <;> rfl
    · split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · split
            · rfl
            · split
              · rfl
              · exact ih _ (by omega) _

theorem next_copy (a : Nat) : highLevelNext (.C a) = (Cap.sourceNext a).map HighLevelState.C := by
  rcases a with _|_|a
  · rfl
  · rfl
  · have he : a+1+1-2=a := by omega
    simpa [highLevelNext,Cap.sourceNext,he] using eval_copy a 1

def embed (n : Nat) : HighLevelState := .C (Cap.oddCounter (n+2))

theorem high_step (n : Nat) : highLevelNext (embed n) = (Cap.sectionNext n).map embed := by
  unfold embed
  rw [next_copy,Cap.odd_transport _ (by omega),←Cap.sectionNext_eq n]
  simp [Option.map_map,Function.comp_def]

theorem acceleration : IsValidAcceleration target 0 (fun n=>highLevelEncode (embed n)) Cap.sectionNext :=
  is_valid_highLevel_acceleration.of_collatz
    (embed := embed)
    (CollatzReachesStar.refl highLevelNext highLevelStart)
    (fun n=>CollatzStepsTo.of_eq (high_step n))

theorem root_criterion : IsHalt target ↔ ∃ i, Cap.rootOf (Cap.halt i)=2 :=
  acceleration.isHalt_iff.trans ((section_halts_iff 0).trans Cap.halt_from_two)
end H421

namespace H252
open BusyBeaver.M_1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_HHH0RE

theorem rules : Cap.TripleRules next State.A2 := by
  constructor <;> intros <;> simp [next]

def embed (n : Nat) : State := .A2 0 1 (2*n)

theorem acceleration : IsValidAcceleration target 3 (fun n=>encode (embed n)) Cap.sectionNext :=
  is_valid_acceleration.of_collatz
    (embed := embed)
    (CollatzReachesStar.refl next start)
    (fun n=>runs_to_steps (Cap.triple_section rules n))

theorem root_criterion : IsHalt target ↔ ∃ i, Cap.rootOf (Cap.halt i)=1 :=
  acceleration.isHalt_iff.trans ((section_halts_iff 3).trans Cap.halt_from_five)
end H252

namespace H754
open BusyBeaver.M_1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_HHH0RE

theorem rules : Cap.TripleRules next State.B2 := by
  constructor <;> intros <;> simp [next]

def embed (n : Nat) : State := .B2 0 1 (2*n)

theorem acceleration : IsValidAcceleration target 1 (fun n=>encode (embed n)) Cap.sectionNext :=
  is_valid_acceleration.of_collatz
    (embed := embed)
    (CollatzReachesStar.refl next start)
    (fun n=>runs_to_steps (Cap.triple_section rules n))

theorem root_criterion : IsHalt target ↔ ∃ i, Cap.rootOf (Cap.halt i)=3 :=
  acceleration.isHalt_iff.trans ((section_halts_iff 1).trans Cap.halt_from_three)
end H754

#print axioms H421.root_criterion
#print axioms H252.root_criterion
#print axioms H754.root_criterion
end CapSource
