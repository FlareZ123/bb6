import Std
import Lean.Elab.Tactic.Omega

namespace RawBridgeAudit

abbrev State := Fin 6
inductive Dir where
  | L | R
  deriving DecidableEq, Repr

def Dir.dx : Dir → Int
  | .L => -1
  | .R => 1

abbrev Instr := Bool × Dir × State
abbrev Machine := State → Bool → Option Instr

def D0 : Machine := fun s bit => match s.val, bit with
  | 0, false => some (true, .R, (1 : State))
  | 0, true => some (false, .R, (4 : State))
  | 1, false => some (true, .L, (2 : State))
  | 1, true => some (false, .R, (0 : State))
  | 2, false => some (true, .L, (0 : State))
  | 2, true => some (true, .L, (3 : State))
  | 3, false => some (true, .L, (2 : State))
  | 3, true => some (true, .L, (5 : State))
  | 4, false => some (false, .L, (2 : State))
  | 4, true => some (false, .L, (1 : State))
  | 5, false => some (true, .L, (4 : State))
  | _, _ => none

/-- State and symbol types used by the pinned external TM62 proof. -/
inductive ExtState where
  | A | B | C | D | E | F
  deriving DecidableEq, Repr

inductive ExtSymbol where
  | S0 | S1
  deriving DecidableEq, Repr

inductive ExtDir where
  | left | right
  deriving DecidableEq, Repr

def encodeState : ExtState → State
  | .A => 0 | .B => 1 | .C => 2 | .D => 3 | .E => 4 | .F => 5

def decodeSymbol : ExtSymbol → Bool
  | .S0 => false | .S1 => true

def encodeDir : ExtDir → Dir
  | .left => .L | .right => .R

abbrev ExtInstr := ExtSymbol × ExtDir × ExtState

def TM62 : ExtState → ExtSymbol → Option ExtInstr := fun q b => match q, b with
  | .A, .S0 => some (.S1, .right, .B)
  | .A, .S1 => some (.S0, .right, .E)
  | .B, .S0 => some (.S1, .left, .C)
  | .B, .S1 => some (.S0, .right, .A)
  | .C, .S0 => some (.S1, .left, .A)
  | .C, .S1 => some (.S1, .left, .D)
  | .D, .S0 => some (.S1, .left, .C)
  | .D, .S1 => some (.S1, .left, .F)
  | .E, .S0 => some (.S0, .left, .C)
  | .E, .S1 => some (.S0, .left, .B)
  | .F, .S0 => some (.S1, .left, .E)
  | .F, .S1 => none

theorem table_conjugate (q : ExtState) (b : ExtSymbol) :
    D0 (encodeState q) (decodeSymbol b) =
      (TM62 q b).map (fun (w,d,s) => (decodeSymbol w, encodeDir d, encodeState s)) := by
  cases q <;> cases b <;> rfl

/-- A Mathlib tape observed in coordinates relative to its current head. -/
abbrev RelTape := Int → ExtSymbol

def relWrite (t : RelTape) (w : ExtSymbol) : RelTape :=
  fun i => if i = 0 then w else t i

def relMove (d : ExtDir) (t : RelTape) : RelTape :=
  match d with
  | .left => fun i => t (i - 1)
  | .right => fun i => t (i + 1)

structure ExtCfg where
  state : ExtState
  head : Int
  tape : RelTape

structure D0Cfg where
  state : State
  head : Int
  tape : Int → Bool

def updateTape (t : Int → Bool) (h : Int) (w : Bool) : Int → Bool :=
  fun i => if i = h then w else t i

/-- Absolute-coordinate interpretation of a head-relative external tape. -/
def absTape (T : RelTape) (h : Int) : Int → Bool :=
  fun i => decodeSymbol (T (i - h))

def absCfg (c : ExtCfg) : D0Cfg :=
  ⟨encodeState c.state, c.head, absTape c.tape c.head⟩

def D0F0Pure (n : Nat) (h : Int) : D0Cfg :=
  ⟨(5 : State), h, fun i => decide (h < i ∧ i ≤ h + (n : Int))⟩

/-- Head-relative tape of the external A(n, []) section, with its head at h. -/
def AEmptyAt (n : Nat) (h : Int) : ExtCfg :=
  ⟨.F, h, fun j => if 0 < j ∧ j ≤ (n : Int) then .S1 else .S0⟩

theorem absCfg_AEmptyAt (n : Nat) (h : Int) :
    absCfg (AEmptyAt n h) = D0F0Pure n h := by
  simp only [absCfg, AEmptyAt, D0F0Pure, encodeState, D0Cfg.mk.injEq]
  refine ⟨trivial, trivial, ?_⟩
  funext i
  change decodeSymbol (if 0 < i - h ∧ i - h ≤ (n : Int) then .S1 else .S0) =
    decide (h < i ∧ i ≤ h + (n : Int))
  by_cases hp : h < i ∧ i ≤ h + (n : Int)
  · have hp' : h < i ∧ i - h ≤ (n : Int) := by omega
    simp [hp, hp', decodeSymbol]
  · have hp' : ¬ (h < i ∧ i - h ≤ (n : Int)) := by omega
    simp [hp, hp', decodeSymbol]

def extStep (c : ExtCfg) : Option ExtCfg :=
  match TM62 c.state (c.tape 0) with
  | none => none
  | some (w,d,s) =>
      some ⟨s, c.head + (encodeDir d).dx, relMove d (relWrite c.tape w)⟩

def d0Step (c : D0Cfg) : Option D0Cfg :=
  match D0 c.state (c.tape c.head) with
  | none => none
  | some (w,d,s) =>
      some ⟨s, c.head + d.dx, updateTape c.tape c.head w⟩

theorem absTape_write_move (T : RelTape) (h : Int) (w : ExtSymbol) (d : ExtDir) :
    (fun i => decodeSymbol (relMove d (relWrite T w) (i - (h + (encodeDir d).dx))) ) =
      updateTape (absTape T h) h (decodeSymbol w) := by
  funext i
  cases d with
  | left =>
      have hi : i - (h + -1) - 1 = i - h := by omega
      simp only [relMove, encodeDir, Dir.dx]
      rw [hi]
      by_cases hp : i = h
      · simp [relWrite, updateTape, decodeSymbol, hp]
      · have hneq : i - h ≠ 0 := by omega
        simp [relWrite, absTape, updateTape, decodeSymbol, hp, hneq]
  | right =>
      have hi : i - (h + 1) + 1 = i - h := by omega
      simp only [relMove, encodeDir, Dir.dx]
      rw [hi]
      by_cases hp : i = h
      · simp [relWrite, updateTape, decodeSymbol, hp]
      · have hneq : i - h ≠ 0 := by omega
        simp [relWrite, absTape, updateTape, decodeSymbol, hp, hneq]

theorem absStep_commute (c : ExtCfg) :
    d0Step (absCfg c) = (extStep c).map absCfg := by
  simp only [d0Step, extStep, absCfg, absTape]
  have hzero : c.head - c.head = 0 := by omega
  rw [hzero]
  have htab := table_conjugate c.state (c.tape 0)
  rw [htab]
  cases h : TM62 c.state (c.tape 0) with
  | none => simp
  | some instr =>
      rcases instr with ⟨w,d,s⟩
      simp only [Option.map_some, absCfg]
      apply congrArg some
      simp only [D0Cfg.mk.injEq]
      exact ⟨trivial, trivial, (absTape_write_move c.tape c.head w d).symm⟩

theorem absStep_halts_iff (c : ExtCfg) :
    d0Step (absCfg c) = none ↔ extStep c = none := by
  rw [absStep_commute]
  cases h : extStep c <;> simp

def extRun : Nat → Option ExtCfg → Option ExtCfg
  | 0, c => c
  | n+1, c => (extRun n c).bind extStep

def d0Run : Nat → Option D0Cfg → Option D0Cfg
  | 0, c => c
  | n+1, c => (d0Run n c).bind d0Step

theorem run_transport (n : Nat) (initial : Option ExtCfg) :
    d0Run n (initial.map absCfg) = (extRun n initial).map absCfg := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [d0Run, extRun, ih]
      cases h : extRun n initial with
      | none => simp
      | some c => simp [absStep_commute]

def ExtHaltsAt (c : ExtCfg) (n : Nat) : Prop :=
  ∃ last, extRun n (some c) = some last ∧ extStep last = none

def D0HaltsAt (c : D0Cfg) (n : Nat) : Prop :=
  ∃ last, d0Run n (some c) = some last ∧ d0Step last = none

theorem haltsAt_transport (c : ExtCfg) (n : Nat) :
    ExtHaltsAt c n ↔ D0HaltsAt (absCfg c) n := by
  constructor
  · rintro ⟨last, hr, hs⟩
    have hrun := run_transport n (some c)
    simp only [Option.map_some, hr] at hrun
    exact ⟨absCfg last, hrun, (absStep_halts_iff last).mpr hs⟩
  · rintro ⟨last, hr, hs⟩
    have hrun := run_transport n (some c)
    have hmap : Option.map absCfg (extRun n (some c)) = some last :=
      hrun.symm.trans hr
    cases he : extRun n (some c) with
    | none => simp [he] at hmap
    | some lastExt =>
        have hlast : absCfg lastExt = last := by simpa [he] using hmap
        refine ⟨lastExt, he, ?_⟩
        have hhalt : d0Step (absCfg lastExt) = none := by rw [hlast]; exact hs
        exact (absStep_halts_iff lastExt).mp hhalt

#print axioms absCfg_AEmptyAt
#print axioms table_conjugate
#print axioms absTape_write_move
#print axioms absStep_commute
#print axioms run_transport
#print axioms haltsAt_transport

theorem halts_transport (c : ExtCfg) :
    (∃ n, ExtHaltsAt c n) ↔ (∃ n, D0HaltsAt (absCfg c) n) := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (haltsAt_transport c n).mp hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, (haltsAt_transport c n).mpr hn⟩

#print axioms halts_transport

end RawBridgeAudit
