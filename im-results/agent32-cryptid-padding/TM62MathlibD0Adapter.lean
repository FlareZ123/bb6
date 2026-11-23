/-
# Draft: Mathlib TM62 → BB6.Bridge → repository D0 adapter

This version reuses the already kernel-checked BB6.Bridge relative/absolute
tape transport rather than duplicating its Int → Bool function-tape proof.
It remains in im-results until the exact pinned Mathlib/upstream closure is
compiled and the transitive axiom profile is inspected.
-/

import Frontier
import RelativeTape
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

def externalMove (w : ExtSymbol) (d : ExtDir) (s : ExtState) : BB6Coverage.Move :=
  { write := encodeSymbol w
    right := match d with | .left => false | .right => true
    next := encodeState s }

def toMove : BB6.Portfolio.Instruction → BB6Coverage.Move
  | (w, .L, s) => { write := w, right := false, next := s }
  | (w, .R, s) => { write := w, right := true, next := s }

/-- The repository's D0 table, viewed in the BB6Coverage raw-step interface. -/
def d0Coverage : BB6Coverage.Machine :=
  fun slot => (BB6.Portfolio.D0 slot.1 slot.2).map toMove

/-- The eleven live source entries agree with the repository's exact D0 table;
F/1 is undefined in both. -/
theorem table_conjugate (q : ExtState) (b : ExtSymbol) :
    BB6.Portfolio.D0 (encodeState q) (encodeSymbol b) =
      (ExternalTM (q, b)).map
        (fun (w, d, s) => (encodeSymbol w, encodeDir d, encodeState s)) := by
  cases q <;> cases b <;> rfl

theorem table_conjugate_coverage (q : ExtState) (b : ExtSymbol) :
    d0Coverage (encodeState q, encodeSymbol b) =
      (ExternalTM (q, b)).map (fun (w, d, s) => externalMove w d s) := by
  unfold d0Coverage
  rw [table_conjugate]
  cases h : ExternalTM (q, b) with
  | none => rfl
  | some instr =>
      rcases instr with ⟨w, d, s⟩
      cases d <;> rfl

/-- Direct representation of a Mathlib tape in the existing relative-tape
bridge: the current cell, cells to the left, and cells to the right. -/
def tapeToRelative (T : ExtTape) : BB6.Bridge.Tape :=
  ⟨encodeSymbol (T.nth 0),
    fun n => encodeSymbol (T.nth (Int.negSucc n)),
    fun n => encodeSymbol (T.nth (Int.ofNat (n + 1)))⟩

theorem tapeToRelative_symbol (T : ExtTape) (i : Int) :
    BB6.Bridge.symbol (tapeToRelative T) i = encodeSymbol (T.nth i) := by
  cases i with
  | ofNat n =>
      cases n with
      | zero => rfl
      | succ n => rfl
  | negSucc n => rfl

/-- Mathlib's write-then-move-right operation is exactly BB6.Bridge.goRight. -/
theorem tapeToRelative_write_move_right (T : ExtTape) (w : ExtSymbol) :
    tapeToRelative (Turing.Tape.move .right (Turing.Tape.write w T)) =
      BB6.Bridge.goRight (tapeToRelative T) (encodeSymbol w) := by
  cases T with
  | mk a leftTape rightTape =>
      simp only [tapeToRelative, BB6.Bridge.goRight,
        BB6.Bridge.Tape.mk.injEq]
      constructor
      · exact by
          change encodeSymbol ((Turing.Tape.move .right
            (Turing.Tape.write w (leftTape {{a}} rightTape))).nth 0) =
            encodeSymbol ((leftTape {{a}} rightTape).nth 1)
          simp [Turing.Tape.move_right_nth, Turing.Tape.write_mk,
            Turing.Tape.nth]
      · constructor
        · exact by
            funext n
            cases n with
            | zero =>
                simp [Turing.Tape.move_right_nth, Turing.Tape.write_mk,
                  Turing.Tape.nth]
            | succ n =>
                simp [Turing.Tape.move_right_nth, Turing.Tape.write_mk,
                  Turing.Tape.nth]
        · exact by
            funext n
            simp [Turing.Tape.move_right_nth, Turing.Tape.write_mk,
              Turing.Tape.nth]

/-- Mathlib's write-then-move-left operation is exactly BB6.Bridge.goLeft. -/
theorem tapeToRelative_write_move_left (T : ExtTape) (w : ExtSymbol) :
    tapeToRelative (Turing.Tape.move .left (Turing.Tape.write w T)) =
      BB6.Bridge.goLeft (tapeToRelative T) (encodeSymbol w) := by
  cases T with
  | mk a leftTape rightTape =>
      simp only [tapeToRelative, BB6.Bridge.goLeft,
        BB6.Bridge.Tape.mk.injEq]
      constructor
      · exact by
          change encodeSymbol ((Turing.Tape.move .left
            (Turing.Tape.write w (leftTape {{a}} rightTape))).nth 0) =
            encodeSymbol ((leftTape {{a}} rightTape).nth (-1))
          simp [Turing.Tape.move_left_nth, Turing.Tape.write_mk,
            Turing.Tape.nth]
      · constructor
        · exact by
            funext n
            simp [Turing.Tape.move_left_nth, Turing.Tape.write_mk,
              Turing.Tape.nth]
        · exact by
            funext n
            cases n with
            | zero =>
                simp [Turing.Tape.move_left_nth, Turing.Tape.write_mk,
                  Turing.Tape.nth]
            | succ n =>
                simp [Turing.Tape.move_left_nth, Turing.Tape.write_mk,
                  Turing.Tape.nth]

structure Positioned where
  state : ExtState
  head : Int
  tape : ExtTape

def project (p : Positioned) : ExtState × ExtTape := (p.state, p.tape)

def toRelative (p : Positioned) : BB6.Bridge.Cfg :=
  ⟨encodeState p.state, p.head, tapeToRelative p.tape⟩

/-- External TM62 step with the absolute head position retained. -/
def step (p : Positioned) : Option Positioned :=
  match ExternalTM (p.state, p.tape.nth 0) with
  | none => none
  | some (w, d, s) =>
      some ⟨s, p.head + (encodeDir d).dx,
        Turing.Tape.move d (Turing.Tape.write w p.tape)⟩

/-- Concrete Mathlib-tape step commutation into the already-proved
relative-tape bridge. -/
theorem step_toRelative (p : Positioned) :
    BB6.Bridge.step d0Coverage (toRelative p) =
      (step p).map toRelative := by
  simp only [BB6.Bridge.step, step, toRelative]
  have hcur : (tapeToRelative p.tape).cur =
      encodeSymbol (p.tape.nth 0) := rfl
  rw [hcur, table_conjugate_coverage]
  cases h : ExternalTM (p.state, p.tape.nth 0) with
  | none =>
      simp [h]
  | some instr =>
      rcases instr with ⟨w, d, s⟩
      cases d with
      | left =>
          simp [toRelative, externalMove, encodeDir, BB6.Portfolio.Dir.dx,
            tapeToRelative_write_move_left]
      | right =>
          simp [toRelative, externalMove, encodeDir, BB6.Portfolio.Dir.dx,
            tapeToRelative_write_move_right]

theorem step_project (p : Positioned) :
    (step p).map project = _root_.step ExternalTM (project p) := by
  cases p with
  | mk q h T =>
      cases T with
      | mk a leftTape rightTape =>
          cases ht : ExternalTM (q, a) with
          | none =>
              simp [step, project, _root_.step, ht, Turing.Tape.nth]
          | some instr =>
              rcases instr with ⟨w, d, s⟩
              cases d <;> simp [step, project, _root_.step, ht, Turing.Tape.nth]

theorem step_none_iff (p : Positioned) :
    step p = none ↔ _root_.step ExternalTM (project p) = none := by
  rw [← step_project p]
  cases step p <;> simp

def run : Nat → Positioned → Option Positioned
  | 0, p => some p
  | n + 1, p => (run n p).bind step

theorem external_stepNat_succ (n : Nat) (c : ExtState × ExtTape) :
    _root_.stepNat ExternalTM (n + 1) c =
      (_root_.stepNat ExternalTM n c).bind (_root_.step ExternalTM) := by
  simp [_root_.stepNat, Nat.repeat]

/-- The positioned run projects to the source's own stepNat, preserving
the exact primitive transition count. -/
theorem run_project (n : Nat) (p : Positioned) :
    (run n p).map project = _root_.stepNat ExternalTM n (project p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change Option.map project ((run n p).bind step) =
        _root_.stepNat ExternalTM (n + 1) (project p)
      rw [Option.map_bind, external_stepNat_succ]
      cases he : run n p with
      | none =>
          have hs : _root_.stepNat ExternalTM n (project p) = none := by
            simpa [he] using ih.symm
          simp [he, hs]
      | some q =>
          have hs : _root_.stepNat ExternalTM n (project p) = some (project q) := by
            simpa [he] using ih.symm
          simp [he, hs, step_project]

def ExtHaltsAt (p : Positioned) (n : Nat) : Prop :=
  ∃ last, run n p = some last ∧ step last = none

theorem extHaltsAt_of_external (p : Positioned) (n : Nat)
    (h : _root_.haltsIn ExternalTM (project p) n) : ExtHaltsAt p n := by
  rcases h with ⟨last, hr, hs⟩
  have hp := run_project n p
  rw [hr] at hp
  cases he : run n p with
  | none => simp [he] at hp
  | some lastExt =>
      have hlast : project lastExt = last := by simpa [he] using hp
      have hs' : _root_.step ExternalTM (project lastExt) = none := by
        simpa [halted, hlast] using hs
      exact ⟨lastExt, he, (step_none_iff lastExt).mpr hs'⟩

def toPortfolioCfg (c : BB6Coverage.Config) : BB6.Portfolio.Cfg :=
  ⟨c.state, c.head, c.tape⟩

/-- The raw BB6Coverage step for d0Coverage is exactly Portfolio.step D0
under the field-for-field configuration conversion. -/
theorem rawStep_toPortfolio (c : BB6Coverage.Config) :
    (BB6Coverage.rawStep d0Coverage c).map toPortfolioCfg =
      BB6.Portfolio.step BB6.Portfolio.D0 (toPortfolioCfg c) := by
  cases h : BB6.Portfolio.D0 c.state (c.tape c.head) with
  | none =>
      simp [BB6Coverage.rawStep, d0Coverage, BB6.Portfolio.step,
        toPortfolioCfg, h]
  | some instr =>
      rcases instr with ⟨w, d, s⟩
      cases d <;>
        simp [BB6Coverage.rawStep, d0Coverage, BB6Coverage.applyMove,
          BB6.Portfolio.step, h, toMove, toPortfolioCfg,
          BB6.Portfolio.Dir.dx]
      all_goals rfl

def toPortfolioAbs (p : Positioned) : BB6.Portfolio.Cfg :=
  toPortfolioCfg (BB6.Bridge.toAbsolute (toRelative p))

/-- One external transition commutes all the way to the repository's D0
absolute-tape semantics. -/
theorem step_toPortfolio (p : Positioned) :
    BB6.Portfolio.step BB6.Portfolio.D0 (toPortfolioAbs p) =
      (step p).map toPortfolioAbs := by
  calc
    BB6.Portfolio.step BB6.Portfolio.D0 (toPortfolioAbs p) =
        (BB6Coverage.rawStep d0Coverage
          (BB6.Bridge.toAbsolute (toRelative p))).map toPortfolioCfg :=
      (rawStep_toPortfolio (BB6.Bridge.toAbsolute (toRelative p))).symm
    _ = (BB6.Bridge.step d0Coverage (toRelative p)).map
          (toPortfolioCfg ∘ BB6.Bridge.toAbsolute) := by
      rw [BB6.Bridge.step_absolute, Option.map_map]
    _ = ((step p).map toRelative).map
          (toPortfolioCfg ∘ BB6.Bridge.toAbsolute) := by
      rw [step_toRelative]
    _ = (step p).map toPortfolioAbs := by
      rw [Option.map_map]
      rfl

/-- Exact-n run transport from the external positioned TM to Portfolio.D0. -/
theorem run_toPortfolio (n : Nat) (p : Positioned) :
    BB6.Portfolio.run BB6.Portfolio.D0 n (some (toPortfolioAbs p)) =
      (run n p).map toPortfolioAbs := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [BB6.Portfolio.run, run, ih]
      cases h : run n p with
      | none => simp [h]
      | some q => simp [h, step_toPortfolio]

def D0HaltsAt (c : BB6.Portfolio.Cfg) (n : Nat) : Prop :=
  ∃ last,
    BB6.Portfolio.run BB6.Portfolio.D0 n (some c) = some last ∧
    BB6.Portfolio.step BB6.Portfolio.D0 last = none

theorem haltsAt_transport (p : Positioned) (n : Nat)
    (h : ExtHaltsAt p n) : D0HaltsAt (toPortfolioAbs p) n := by
  rcases h with ⟨last, hr, hs⟩
  have hrun : BB6.Portfolio.run BB6.Portfolio.D0 n (some (toPortfolioAbs p)) =
      some (toPortfolioAbs last) := by
    simpa [hr] using run_toPortfolio n p
  have hhalt : BB6.Portfolio.step BB6.Portfolio.D0 (toPortfolioAbs last) = none := by
    simpa [hs] using step_toPortfolio last
  exact ⟨toPortfolioAbs last, hrun, hhalt⟩

/-- The source section A(n,[]) has n ones to the right of its blank
scanned cell and is blank at every nonpositive relative coordinate. -/
theorem singletonPow_replicate (n : Nat) :
    ([_root_.Symbol.S1] : List _root_.Symbol) ^ n =
      List.replicate n _root_.Symbol.S1 := by
  change Nat.repeat (fun xs : List _root_.Symbol => _root_.Symbol.S1 :: xs) n [] =
    List.replicate n _root_.Symbol.S1
  induction n with
  | zero => rfl
  | succ n ih => simp [Nat.repeat, ih, List.replicate_succ]

private theorem default_symbol : (default : _root_.Symbol) = _root_.Symbol.S0 := rfl

theorem getI_replicate (n i : Nat) :
    (List.replicate n _root_.Symbol.S1).getI i =
      if i < n then _root_.Symbol.S1 else _root_.Symbol.S0 := by
  by_cases hi : i < n
  · have hlen : i < (List.replicate n _root_.Symbol.S1).length := by simpa using hi
    rw [List.getI_eq_getElem _ hlen]
    simp [List.getElem_replicate, hi]
  · have hlen : (List.replicate n _root_.Symbol.S1).length ≤ i := by
      simpa using Nat.le_of_not_gt hi
    rw [List.getI_eq_default _ hlen, default_symbol]
    simp [hi]

theorem A_tape_nth (n : Nat) (j : Int) :
    ((«1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---».A n []).2).nth j =
      if 0 < j ∧ j ≤ (n : Int) then _root_.Symbol.S1 else _root_.Symbol.S0 := by
  have hdefault : (default : Turing.ListBlank _root_.Symbol) =
      Turing.ListBlank.mk [] := rfl
  cases j with
  | ofNat j =>
      cases j with
      | zero =>
          simp [«1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---».A,
            Turing.Tape.nth, hdefault, default_symbol]
      | succ j =>
          simp only [«1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---».A,
            Turing.Tape.nth, hdefault, Turing.ListBlank.append_mk,
            Turing.ListBlank.nth_mk, List.append_nil]
          have hOne : (1 : _root_.Symbol) = _root_.Symbol.S1 := rfl
          have hpow : ([1] : List _root_.Symbol) ^ n =
              List.replicate n _root_.Symbol.S1 := by
            rw [hOne]
            exact singletonPow_replicate n
          rw [hpow, getI_replicate n j]
          have hbound : ((j : Int) + 1 ≤ (n : Int)) ↔ j < n := by
            constructor
            · intro h
              have h' : j + 1 ≤ n := by exact_mod_cast h
              omega
            · intro h
              have h' : j + 1 ≤ n := by omega
              exact_mod_cast h'
          simp [hbound]
  | negSucc j =>
      simp [«1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---».A,
        Turing.Tape.nth, «1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---».default_tail,
        hdefault, default_symbol]

def ofA (n : Nat) (h : Int) : Positioned :=
  ⟨_root_.State.F, h, («1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---».A n []).2⟩

theorem project_ofA (n : Nat) (h : Int) :
    project (ofA n h) = «1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---».A n [] := by
  rfl

theorem toPortfolioAbs_ofA (n : Nat) (h : Int) :
    toPortfolioAbs (ofA n h) = BB6.Portfolio.F0Pure n h := by
  simp only [toPortfolioAbs, toPortfolioCfg, BB6.Bridge.toAbsolute,
    toRelative, encodeState, BB6.Portfolio.F0Pure, BB6.Portfolio.Cfg.mk.injEq,
    ofA]
  refine ⟨trivial, trivial, ?_⟩
  funext x
  rw [tapeToRelative_symbol]
  change encodeSymbol (((«1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---».A n []).2).nth (x - h)) = _
  rw [A_tape_nth n (x - h)]
  by_cases h₁ : h < x <;> by_cases h₂ : x ≤ h + (n : Int) <;>
    simp [encodeSymbol, Int.add_comm, h₁, h₂]

/-- The external halting cylinder transfers to the exact repository D0
configuration at the same primitive halting time. This is not a blank-root
reachability theorem. -/
theorem D0_halts_on_A_cylinder (k : Nat) (h : Int) :
    ∃ n, D0HaltsAt
      (BB6.Portfolio.F0Pure
        (3 ^ 108 * k + 1975700577069254261393123959451562008800234946348086) h) n := by
  let m := 3 ^ 108 * k + 1975700577069254261393123959451562008800234946348086
  obtain ⟨n, hn⟩ :=
    «1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---».halts_A_mod_3_pow_108 k
  have hsource : _root_.haltsIn ExternalTM (project (ofA m h)) n := by
    simpa only [ExternalTM, project_ofA] using hn
  have hext : ExtHaltsAt (ofA m h) n :=
    extHaltsAt_of_external (ofA m h) n hsource
  have hd0 := haltsAt_transport (ofA m h) n hext
  exact ⟨n, by simpa [m, toPortfolioAbs_ofA] using hd0⟩

#print axioms table_conjugate
#print axioms table_conjugate_coverage
#print axioms tapeToRelative_symbol
#print axioms tapeToRelative_write_move_right
#print axioms tapeToRelative_write_move_left
#print axioms step_toRelative
#print axioms step_project
#print axioms run_project
#print axioms rawStep_toPortfolio
#print axioms step_toPortfolio
#print axioms run_toPortfolio
#print axioms A_tape_nth
#print axioms toPortfolioAbs_ofA
#print axioms D0_halts_on_A_cylinder

end BB6.CryptidD0Bridge
