import BusyBeaver.BB6.Accelerations.M_1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LFHHH_1LD1LF

namespace BusyBeaver.M_1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LFHHH_1LD1LF
open BusyBeaver.Stack

/-- A left zero-run stack has no leading zero, so E is not a halt-gate state. -/
def goodL : List Nat → Prop
  | 0 :: _ => False
  | _ => True

def goodS : State → Prop
  | .E L _ => goodL L

/-- A possible zero-leading F-sweep exit: zeros followed by 2,0. -/
def core : List Nat → Prop
  | 0 :: xs => core xs
  | 2 :: 0 :: _ => True
  | _ => False

theorem good_inc (L : List Nat) : goodL (incRun L) := by
  cases L with
  | nil => trivial
  | cons n xs => simp [incRun, goodL]

/-- Every inner right-mode sweep remains safe whenever it is in a safe
    A- or C-mode, or in arbitrary B-mode. -/
theorem elem_good (stepRt : RightMode → List Nat → State) (Rt : List Nat)
    (hAr : ∀ L, goodL L → goodS (stepRt .ar L))
    (hBr : ∀ L, goodS (stepRt .br L))
    (_hCr : ∀ L, goodL L → goodS (stepRt .cr L)) (d : Nat) :
    (∀ L, goodL L → goodS (sweepElem stepRt d .ar L Rt)) ∧
    (∀ L, goodS (sweepElem stepRt d .br L Rt)) ∧
    (∀ L, goodL L → goodS (sweepElem stepRt d .cr L Rt)) := by
  induction d with
  | zero =>
      constructor
      · intro L h; simpa [sweepElem, goodS] using h
      constructor
      · intro L; exact hAr (incRun L) (good_inc L)
      · intro L _; exact hBr (0 :: L)
  | succ d ih =>
      constructor
      · intro L _; exact ih.2.1 (0 :: L)
      constructor
      · intro L; exact ih.2.2 (incRun L) (good_inc L)
      · intro L h
        cases d with
        | zero => exact hBr (1 :: L)
        | succ d => simpa [sweepElem, goodS] using h

theorem right_good (R : List Nat) :
    (∀ L, goodL L → goodS (sweepRight .ar L R)) ∧
    (∀ L, goodS (sweepRight .br L R)) ∧
    (∀ L, goodL L → goodS (sweepRight .cr L R)) := by
  induction R with
  | nil =>
      constructor
      · intro L _; trivial
      constructor
      · intro L; exact good_inc L
      · intro L h; exact h
  | cons d Rt ih =>
      rcases ih with ⟨ha, hb, hc⟩
      have he := elem_good (fun m' L' => sweepRight m' L' Rt) Rt ha hb hc d
      exact he

/-- The right sweep begun with a 2 is always gate-safe regardless of the
    left-stack contents, thanks to the enforced intermediate B mode. -/
theorem ar_two_good (L R : List Nat) :
    goodS (sweepRight .ar L (2 :: R)) := by
  have he : sweepRight .ar L (2 :: R) =
      sweepRight .br (0 :: incRun (0 :: L)) R := rfl
  rw [he]
  exact (right_good R).2.1 _

/-- Exact all-input and all-right-stack criterion for the F sweep to
    produce an E state with a zero leading left-run. -/
theorem fl_good_iff (L : List Nat) : ∀ R : List Nat,
    goodS (sweepFL L R) ↔ ¬core L := by
  induction L with
  | nil =>
      intro R
      constructor
      · intro _; simp [core]
      · intro _; exact ar_two_good [] R
  | cons a Lt ih =>
      intro R
      rcases a with _ | _ | _ | a
      · simpa only [sweepFL, core] using ih (0 :: R)
      · constructor
        · intro _; simp [core]
        · intro _; exact (right_good (0 :: R)).2.1 _
      · cases Lt with
        | nil => simp [sweepFL, core, goodS, goodL]
        | cons b Bs =>
          cases b with
          | zero => simp [sweepFL, core, goodS, goodL]
          | succ b => simp [sweepFL, core, goodS, goodL]
      · constructor
        · intro _; simp [core]
        · intro _; exact ar_two_good (a :: Lt) R

theorem output_gate_iff_not_good (s : State) :
    (∃ L R, s = .E (0 :: L) R) ↔ ¬goodS s := by
  cases s with
  | E L R =>
    cases L with
    | nil => simp [goodS, goodL]
    | cons n Lt =>
      cases n with
      | zero => simp [goodS, goodL]
      | succ n => simp [goodS, goodL]

theorem live_next_gate_iff_core (a : Nat) (Lt R : List Nat) :
    (∃ L' R', next (.E ((a + 1) :: Lt) R) = some (.E (0 :: L') R')) ↔
       core (a :: Lt) := by
  simp only [next, Option.some.injEq]
  rw [output_gate_iff_not_good]
  have h := fl_good_iff (a :: Lt) (0 :: R)
  constructor
  · intro hn
    exact Classical.byContradiction (fun hc => hn (h.mpr hc))
  · intro hc hg
    exact (h.mp hg) hc

/-- Complete one-section precursor language: leading 3,0 or
    leading 1, then any number of zeros, then 2,0. -/
def preGate : List Nat → Prop
  | 1 :: Lt => core Lt
  | 3 :: 0 :: _ => True
  | _ => False

theorem next_gate_iff (L R : List Nat) :
    (∃ L' R', next (.E L R) = some (.E (0 :: L') R')) ↔ preGate L := by
  cases L with
  | nil =>
      constructor
      · rintro ⟨L',R',h⟩
        have hs : ¬goodS (sweepFL [] (0 :: R)) := by
          apply (output_gate_iff_not_good _).mp
          exact ⟨L',R',Option.some.inj h⟩
        have hg : goodS (sweepFL [] (0 :: R)) :=
          (fl_good_iff [] (0 :: R)).mpr (by simp [core])
        exact False.elim (hs hg)
      · intro h; exact False.elim h
  | cons n Lt =>
      cases n with
      | zero => simp [next, preGate]
      | succ n =>
        have h := live_next_gate_iff_core n Lt R
        cases n with
        | zero => simpa [preGate, core] using h
        | succ n =>
          cases n with
          | zero => simpa [preGate, core] using h
          | succ n =>
            cases n with
            | zero =>
              cases Lt with
              | nil => simpa [preGate, core] using h
              | cons b Bs =>
                cases b with
                | zero => simpa [preGate, core] using h
                | succ b => simpa [preGate, core] using h
            | succ n => simpa [preGate, core] using h

/-- Fully explicit regular-language form of the F-sweep core condition. -/
theorem core_iff_regex (L : List Nat) :
    core L ↔ ∃ n tail, L = List.replicate n 0 ++ (2 :: 0 :: tail) := by
  induction L with
  | nil =>
      constructor
      · intro h; exact False.elim h
      · rintro ⟨n,tail,h⟩
        cases n with
        | zero => simp at h
        | succ n => simp at h
  | cons a Lt ih =>
      cases a with
      | zero =>
          constructor
          · intro h
            obtain ⟨n,tail,hlist⟩ := ih.mp (by simpa [core] using h)
            exact ⟨n+1,tail,by simp [List.replicate_succ, hlist]⟩
          · rintro ⟨n,tail,hlist⟩
            cases n with
            | zero => simp at hlist
            | succ n =>
                have htail : Lt = List.replicate n 0 ++ (2 :: 0 :: tail) := by
                  simpa using congrArg List.tail hlist
                exact ih.mpr ⟨n,tail,htail⟩
      | succ a =>
          constructor
          · intro h
            cases a with
            | zero => exact False.elim h
            | succ a =>
                cases a with
                | zero =>
                    cases Lt with
                    | nil => exact False.elim h
                    | cons b Bs =>
                        cases b with
                        | zero => exact ⟨0,Bs,rfl⟩
                        | succ b => exact False.elim h
                | succ a => exact False.elim h
          · rintro ⟨n,tail,hlist⟩
            cases n with
            | zero =>
                cases a with
                | zero => simp at hlist
                | succ a =>
                    cases a with
                    | zero =>
                        cases Lt with
                        | nil => simp at hlist
                        | cons b Bs =>
                            cases b with
                            | zero => trivial
                            | succ b => simp at hlist
                    | succ a => simp at hlist
            | succ n =>
                have hh := congrArg List.head? hlist
                simp [List.replicate_succ] at hh

#print axioms right_good
#print axioms fl_good_iff
#print axioms next_gate_iff
#print axioms core_iff_regex
end BusyBeaver.M_1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LFHHH_1LD1LF
