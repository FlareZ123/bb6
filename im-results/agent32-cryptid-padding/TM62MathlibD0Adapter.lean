/-!
# Draft: actual Mathlib Tape adapter for external TM62 → repository D0

This file is intentionally kept under im-results until the complete pinned
upstream/Mathlib dependency closure has been compiled and its axiom profile
inspected. The abstract function-tape square is already kernel-checked in
Agent 4's HeadRelativeFunctionAudit.lean; this file is the concrete
Turing.Tape integration, not a new blank-root result.
-/

import Mathlib.Computability.TuringMachine.Tape
import MachineConjugacy
import DTableWitness
import DStartFinite
import BusyLean.Individual.«1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---»

namespace BB6.CryptidD0Bridge

abbrev ExtState := _root_.State
abbrev ExtSymbol := _root_.Symbol
abbrev ExtDir := Turing.Dir
abbrev ExtTape := Turing.Tape ExtSymbol

abbrev ExternalTM : ExtState × ExtSymbol → Option (ExtSymbol × ExtDir × ExtState) :=
  «1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---».tm

def encodeState : ExtState → BB6.Portfolio.State
  | .A => 0
  | .B => 1
  | .C => 2
  | .D => 3
  | .E => 4
  | .F => 5

def encodeSymbol : ExtSymbol → Bool
  | .S0 => false
  | .S1 => true

def encodeDir : ExtDir → BB6.Portfolio.Dir
  | .left => .L
  | .right => .R

/-- The eleven live source entries agree with the repository's exact six-state D0 table;
F/1 is undefined in both. -/
theorem table_conjugate (q : ExtState) (b : ExtSymbol) :
    BB6.Portfolio.D0 (encodeState q) (encodeSymbol b) =
      (ExternalTM (q, b)).map
        (fun (w, d, s) => (encodeSymbol w, encodeDir d, encodeState s)) := by
  cases q <;> cases b <;> rfl

structure ExtCfg where
  state : ExtState
  head : Int
  tape : ExtTape

def project (c : ExtCfg) : ExtState × ExtTape := (c.state, c.tape)

/-- Absolute-coordinate view of a head-relative Mathlib tape. -/
def absTape (T : ExtTape) (h : Int) : Int → Bool :=
  fun i => encodeSymbol (T.nth (i - h))

def absCfg (c : ExtCfg) : BB6.Portfolio.Cfg :=
  ⟨encodeState c.state, c.head, absTape c.tape c.head⟩

/-- External TM.step writes the new symbol before moving the tape. -/
def extStep (c : ExtCfg) : Option ExtCfg :=
  match ExternalTM (c.state, c.tape.nth 0) with
  | none => none
  | some (w, d, s) =>
      some ⟨s, c.head + (encodeDir d).dx,
        Turing.Tape.move d (Turing.Tape.write w c.tape)⟩

/-- The actual Mathlib write/move adapter, with the absolute head updated
by the same direction as the source machine. -/
theorem absTape_write_move (T : ExtTape) (h : Int) (w : ExtSymbol) (d : ExtDir) :
    absTape (Turing.Tape.move d (Turing.Tape.write w T))
        (h + (encodeDir d).dx) =
      BB6.Portfolio.updateTape (absTape T h) h (encodeSymbol w) := by
  funext i
  cases d with
  | left =>
      have hidx : i - (h + -1) - 1 = i - h := by omega
      simp only [absTape, encodeDir, BB6.Portfolio.Dir.dx, Turing.Tape.move_left_nth]
      rw [hidx]
      by_cases hp : i = h
      · subst i
        simp [BB6.Portfolio.updateTape, Turing.Tape.write_nth, encodeSymbol]
      · have hneq : i - h ≠ 0 := by omega
        simp [BB6.Portfolio.updateTape, Turing.Tape.write_nth, encodeSymbol, hp, hneq]
  | right =>
      have hidx : i - (h + 1) + 1 = i - h := by omega
      simp only [absTape, encodeDir, BB6.Portfolio.Dir.dx, Turing.Tape.move_right_nth]
      rw [hidx]
      by_cases hp : i = h
      · subst i
        simp [BB6.Portfolio.updateTape, Turing.Tape.write_nth, encodeSymbol]
      · have hneq : i - h ≠ 0 := by omega
        simp [BB6.Portfolio.updateTape, Turing.Tape.write_nth, encodeSymbol, hp, hneq]

/-- One source transition commutes with the repository's raw D0 step,
including the shared undefined F/1 transition. -/
theorem absStep_commute (c : ExtCfg) :
    BB6.Portfolio.step BB6.Portfolio.D0 (absCfg c) =
      (extStep c).map absCfg := by
  simp only [BB6.Portfolio.step, absCfg, absTape, Int.sub_self, Turing.Tape.nth_zero]
  rw [table_conjugate]
  cases h : ExternalTM (c.state, c.tape.nth 0) with
  | none =>
      simp [extStep, h]
  | some instr =>
      rcases instr with ⟨w, d, s⟩
      simp [extStep, h, encodeDir, BB6.Portfolio.Dir.dx, absTape_write_move]

theorem absStep_halts_iff (c : ExtCfg) :
    BB6.Portfolio.step BB6.Portfolio.D0 (absCfg c) = none ↔ extStep c = none := by
  rw [absStep_commute]
  cases h : extStep c <;> simp [h]

/-- Extended external run, retaining the absolute head coordinate. -/
def extRun : Nat → Option ExtCfg → Option ExtCfg
  | 0, c => c
  | n + 1, c => (extRun n c).bind extStep

/-- Exact-n run transport into the repository's infinite-tape D0 model. -/
theorem run_transport (n : Nat) (initial : Option ExtCfg) :
    BB6.Portfolio.run BB6.Portfolio.D0 n (initial.map absCfg) =
      (extRun n initial).map absCfg := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [BB6.Portfolio.run, extRun, ih]
      cases h : extRun n initial with
      | none => simp
      | some c => simp [absStep_commute]

def ExtHaltsAt (c : ExtCfg) (n : Nat) : Prop :=
  ∃ last, extRun n (some c) = some last ∧ extStep last = none

def D0HaltsAt (c : BB6.Portfolio.Cfg) (n : Nat) : Prop :=
  ∃ last,
    BB6.Portfolio.run BB6.Portfolio.D0 n (some c) = some last ∧
    BB6.Portfolio.step BB6.Portfolio.D0 last = none

theorem haltsAt_transport (c : ExtCfg) (n : Nat) :
    ExtHaltsAt c n ↔ D0HaltsAt (absCfg c) n := by
  constructor
  · rintro ⟨last, hr, hs⟩
    have hrun := run_transport n (some c)
    simp only [Option.map_some, hr] at hrun
    exact ⟨absCfg last, hrun, (absStep_halts_iff last).2 hs⟩
  · rintro ⟨last, hr, hs⟩
    have hrun := run_transport n (some c)
    have hmap : (extRun n (some c)).map absCfg = some last := hrun.symm.trans hr
    cases he : extRun n (some c) with
    | none => simp [he] at hmap
    | some lastExt =>
        have hlast : absCfg lastExt = last := by simpa [he] using hmap
        refine ⟨lastExt, he, ?_⟩
        exact (absStep_halts_iff lastExt).mp (by simpa [hlast] using hs)

/-- Forgetting the absolute head coordinate recovers the external source step. -/
theorem extStep_project (c : ExtCfg) :
    (extStep c).map project = _root_.step ExternalTM (project c) := by
  cases c with
  | mk q h T =>
      cases T with
      | mk a L R =>
          cases ht : ExternalTM (q, a) with
          | none => simp [extStep, project, _root_.step, ht]
          | some instr =>
              rcases instr with ⟨w, d, s⟩
              simp [extStep, project, _root_.step, ht,
                Turing.Tape.write, Turing.Tape.move]

theorem extStep_none_iff (c : ExtCfg) :
    extStep c = none ↔ _root_.step ExternalTM (project c) = none := by
  cases c with
  | mk q h T =>
      cases T with
      | mk a L R =>
          cases ht : ExternalTM (q, a) <;>
            simp [extStep, project, _root_.step, ht]

theorem external_stepNat_succ (n : Nat) (c : ExtState × ExtTape) :
    _root_.stepNat ExternalTM (n + 1) c =
      (_root_.stepNat ExternalTM n c).bind (_root_.step ExternalTM) := by
  simp [_root_.stepNat, Nat.repeat]

/-- The extended run projects to the source's own stepNat, with no time offset. -/
theorem extRun_project (n : Nat) (c : ExtCfg) :
    (extRun n (some c)).map project = _root_.stepNat ExternalTM n (project c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change Option.map project ((extRun n (some c)).bind extStep) =
        _root_.stepNat ExternalTM (n + 1) (project c)
      rw [Option.map_bind, external_stepNat_succ]
      cases he : extRun n (some c) with
      | none =>
          have hs : _root_.stepNat ExternalTM n (project c) = none := by
            simpa [he] using ih.symm
          simp [he, hs]
      | some c' =>
          have hs : _root_.stepNat ExternalTM n (project c) = some (project c') := by
            simpa [he] using ih.symm
          simp [he, hs, extStep_project]

theorem extHaltsAt_iff_external (c : ExtCfg) (n : Nat) :
    ExtHaltsAt c n ↔ _root_.haltsIn ExternalTM (project c) n := by
  constructor
  · rintro ⟨last, hr, hs⟩
    refine ⟨project last, ?_, ?_⟩
    · simpa [hr] using (extRun_project n c).symm
    · exact (extStep_none_iff last).mp hs
  · rintro ⟨last, hr, hs⟩
    have hp := extRun_project n c
    rw [hr] at hp
    cases he : extRun n (some c) with
    | none => simp [he] at hp
    | some lastExt =>
        have hlast : project lastExt = last := by simpa [he] using hp
        refine ⟨lastExt, he, ?_⟩
        exact (extStep_none_iff lastExt).mpr (by simpa [hlast] using hs)

/-- The source section A(n,[]) has exactly n ones to the right of its
blank scanned cell, and is blank at every nonpositive relative coordinate. -/
theorem singletonPow_replicate (n : Nat) :
    ([_root_.Symbol.S1] : List _root_.Symbol) ^ n =
      List.replicate n _root_.Symbol.S1 := by
  change Nat.repeat (fun xs : List _root_.Symbol => _root_.Symbol.S1 :: xs) n [] =
    List.replicate n _root_.Symbol.S1
  induction n with
  | zero => rfl
  | succ n ih => simp [Nat.repeat, ih, List.replicate_succ]

theorem getI_replicate (n i : Nat) :
    (List.replicate n _root_.Symbol.S1).getI i =
      if i < n then _root_.Symbol.S1 else _root_.Symbol.S0 := by
  by_cases hi : i < n
  · have hlen : i < (List.replicate n _root_.Symbol.S1).length := by simpa using hi
    rw [List.getI_eq_getElem hlen]
    simp [List.getElem_replicate, hi]
  · have hlen : (List.replicate n _root_.Symbol.S1).length ≤ i := by
      simpa using Nat.le_of_not_gt hi
    rw [List.getI_eq_default hlen]
    simp [hi]

theorem A_tape_nth (n : Nat) (j : Int) :
    ((«1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---».A n []).2).nth j =
      if 0 < j ∧ j ≤ (n : Int) then _root_.Symbol.S1 else _root_.Symbol.S0 := by
  cases j with
  | ofNat j =>
      cases j with
      | zero =>
          simp [«1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---».A, Turing.Tape.nth]
      | succ j =>
          simp only [«1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---».A,
            Turing.Tape.nth, Turing.ListBlank.append_mk, Turing.ListBlank.nth_mk,
            List.nil_append, singletonPow_replicate]
          change (List.replicate n _root_.Symbol.S1).getI j =
            if 0 < (Int.ofNat (j + 1)) ∧ (Int.ofNat (j + 1)) ≤ (n : Int)
              then _root_.Symbol.S1 else _root_.Symbol.S0
          have hpos : (0 : Int) < (Int.ofNat (j + 1)) := by omega
          have hbound : (Int.ofNat (j + 1) ≤ (n : Int)) ↔ j < n := by omega
          simp [getI_replicate, hpos, hbound]
  | negSucc j =>
      simp [«1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---».A,
        Turing.Tape.nth, «1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---».default_tail]

def ofA (n : Nat) (h : Int) : ExtCfg :=
  ⟨_root_.State.F, h, («1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---».A n []).2⟩

theorem project_ofA (n : Nat) (h : Int) :
    project (ofA n h) = «1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---».A n [] := by
  rfl

theorem absCfg_ofA (n : Nat) (h : Int) :
    absCfg (ofA n h) = BB6.Portfolio.F0Pure n h := by
  simp only [absCfg, ofA, encodeState, absTape, BB6.Portfolio.F0Pure,
    BB6.Portfolio.Cfg.mk.injEq]
  refine ⟨rfl, rfl, ?_⟩
  funext i
  rw [A_tape_nth n (i - h)]
  by_cases hp : h < i ∧ i ≤ h + (n : Int)
  · have hq : 0 < i - h ∧ i - h ≤ (n : Int) := by omega
    simp [encodeSymbol, hp, hq]
  · have hq : ¬ (0 < i - h ∧ i - h ≤ (n : Int)) := by omega
    simp [encodeSymbol, hp, hq]

/-- D0 inherits the external conditional halting cylinder at exactly the
same primitive halting time. This does not assert that the blank root reaches it. -/
theorem D0_halts_on_A_cylinder (k : Nat) (h : Int) :
    ∃ n, D0HaltsAt
      (BB6.Portfolio.F0Pure
        (3 ^ 108 * k + 1975700577069254261393123959451562008800234946348086) h) n := by
  let m := 3 ^ 108 * k + 1975700577069254261393123959451562008800234946348086
  obtain ⟨n, hn⟩ :=
    «1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---».halts_A_mod_3_pow_108 k
  have hext : ExtHaltsAt (ofA m h) n := by
    apply (extHaltsAt_iff_external (ofA m h) n).2
    simpa [project_ofA] using hn
  have hd0 := (haltsAt_transport (ofA m h) n).mp hext
  simpa [m, absCfg_ofA] using hd0

#print axioms table_conjugate
#print axioms absTape_write_move
#print axioms absStep_commute
#print axioms run_transport
#print axioms haltsAt_transport
#print axioms extStep_project
#print axioms extRun_project
#print axioms A_tape_nth
#print axioms absCfg_ofA
#print axioms D0_halts_on_A_cylinder

end BB6.CryptidD0Bridge
