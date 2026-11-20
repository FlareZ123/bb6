import Frontier
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.DirectFiveSlot
open BB6Coverage

def a0 : Slot := (⟨0, by decide⟩, false)
def b0 : Slot := (⟨1, by decide⟩, false)
def c1 : Slot := (⟨2, by decide⟩, true)
def d1 : Slot := (⟨3, by decide⟩, true)
def e0 : Slot := (⟨4, by decide⟩, false)

def a0Action : Transition := some ⟨true, true, 1⟩
def b0Action : Transition := some ⟨true, false, 2⟩
def c1Action : Transition := some ⟨false, true, 3⟩
def d1Action : Transition := some ⟨true, true, 4⟩
def e0Action : Transition := some ⟨true, false, 2⟩

def p0 : PartialMachine := emptyTable
def p1 : PartialMachine := refine p0 a0 a0Action
def p2 : PartialMachine := refine p1 b0 b0Action
def p3 : PartialMachine := refine p2 c1 c1Action
def p4 : PartialMachine := refine p3 d1 d1Action
def fiveSlot : PartialMachine := refine p4 e0 e0Action

def cConfig (k : Nat) : Config :=
  { state := ⟨2, by decide⟩
    head := (k : Int)
    tape := fun x => x = (k : Int) ∨ x = (k : Int) + 1 }

def dMove : Move := ⟨false, true, 3⟩
def eMove : Move := ⟨true, true, 4⟩
def cMove : Move := ⟨false, true, 3⟩
def backMove : Move := ⟨true, false, 2⟩

def dConfig (k : Nat) : Config := applyMove (cConfig k) cMove
def eConfig (k : Nat) : Config := applyMove (dConfig k) eMove

theorem cConfig_reads_c1 (k : Nat) : readSlot (cConfig k) = c1 := by
  simp [readSlot, cConfig, c1]

theorem dConfig_reads_d1 (k : Nat) : readSlot (dConfig k) = d1 := by
  simp [readSlot, dConfig, applyMove, cConfig, cMove, d1]
  have h : (k : Int) + 1 ≠ (k : Int) := by omega
  exact h

theorem eConfig_reads_e0 (k : Nat) : readSlot (eConfig k) = e0 := by
  simp [readSlot, eConfig, dConfig, applyMove, cConfig, cMove, eMove, e0]
  have h1 : (k : Int) + 1 ≠ (k : Int) := by omega
  have h2 : (k : Int) + 2 ≠ (k : Int) := by omega
  have h3 : (k : Int) + 2 ≠ (k : Int) + 1 := by omega
  constructor
  · exact h1
  · intro _
    exact ⟨h2, h1⟩

theorem cycle_config (k : Nat) : applyMove (eConfig k) backMove = cConfig (k+1) := by
  simp [eConfig, dConfig, cConfig, applyMove, cMove, eMove, backMove]
  constructor
  · omega
  · funext x
    by_cases h0 : x = (k : Int)
    · subst x
      simp [Bool.or_comm]
    · by_cases h1 : x = (k : Int) + 1
      · subst x
        have h10 : (k : Int) + 1 ≠ (k : Int) := by omega
        simp [h10, Bool.or_comm]
      · by_cases h2 : x = (k : Int) + 2
        · subst x
          have h20 : (k : Int) + 2 ≠ (k : Int) := by omega
          have h21 : (k : Int) + 2 ≠ (k : Int) + 1 := by omega
          simp [h20, h21, Bool.or_comm]
        · simp [h0, h1, Bool.or_comm]

set_option linter.unusedSimpArgs false in
theorem assigned_actions (m : Machine) (hm : compatible fiveSlot m) :
    m a0 = a0Action ∧ m b0 = b0Action ∧ m c1 = c1Action ∧
      m d1 = d1Action ∧ m e0 = e0Action := by
  have hA : fiveSlot a0 = some a0Action := by
    simp [fiveSlot, p4, p3, p2, p1, p0, refine, a0, b0, c1, d1, e0]
  have hB : fiveSlot b0 = some b0Action := by
    simp [fiveSlot, p4, p3, p2, p1, p0, refine, a0, b0, c1, d1, e0]
  have hC : fiveSlot c1 = some c1Action := by
    simp [fiveSlot, p4, p3, p2, p1, p0, refine, a0, b0, c1, d1, e0]
  have hD : fiveSlot d1 = some d1Action := by
    simp [fiveSlot, p4, p3, p2, p1, p0, refine, a0, b0, c1, d1, e0]
  have hE : fiveSlot e0 = some e0Action := by
    simp [fiveSlot, p4, p3, p2, p1, p0, refine, a0, b0, c1, d1, e0]
  exact ⟨hm a0 a0Action hA, hm b0 b0Action hB, hm c1 c1Action hC,
    hm d1 d1Action hD, hm e0 e0Action hE⟩

theorem c_step (m : Machine) (hm : compatible fiveSlot m) (k : Nat) :
    rawStep m (cConfig k) = some (dConfig k) := by
  have ha := (assigned_actions m hm).2.2.1
  unfold rawStep
  rw [cConfig_reads_c1, ha]
  simp [c1Action, dConfig, cMove]

theorem d_step (m : Machine) (hm : compatible fiveSlot m) (k : Nat) :
    rawStep m (dConfig k) = some (eConfig k) := by
  have ha := (assigned_actions m hm).2.2.2.1
  unfold rawStep
  rw [dConfig_reads_d1, ha]
  simp [d1Action, eConfig, eMove]

theorem e_step (m : Machine) (hm : compatible fiveSlot m) (k : Nat) :
    rawStep m (eConfig k) = some (cConfig (k+1)) := by
  have ha := (assigned_actions m hm).2.2.2.2
  unfold rawStep
  rw [eConfig_reads_e0, ha]
  simp only [e0Action, Option.map_some]
  exact congrArg some (cycle_config k)

theorem run_c_1 (m : Machine) (hm : compatible fiveSlot m) (k : Nat) :
    run m 1 (cConfig k) = some (dConfig k) := by
  simp [run, c_step m hm k]

theorem run_c_2 (m : Machine) (hm : compatible fiveSlot m) (k : Nat) :
    run m 2 (cConfig k) = some (eConfig k) := by
  rw [run, run_c_1 m hm k]
  simp [d_step m hm k]

theorem run_c_3 (m : Machine) (hm : compatible fiveSlot m) (k : Nat) :
    run m 3 (cConfig k) = some (cConfig (k+1)) := by
  rw [run, run_c_2 m hm k]
  simp [e_step m hm k]

theorem run_compose (m : Machine) (c : Config) (n k : Nat) :
    run m (n+k) c = (run m n c).bind (fun d => run m k d) := by
  induction k with
  | zero => simp [run]
  | succ k ih =>
      rw [Nat.add_succ, run, ih]
      simp [run, Option.bind_assoc]

def bConfig : Config := applyMove blank ⟨true, true, 1⟩

theorem bConfig_to_cConfig : applyMove bConfig ⟨true, false, 2⟩ = cConfig 0 := by
  simp [bConfig, cConfig, blank, applyMove]
  funext x
  by_cases h0 : x = 0
  · subst x
    simp
  · simp [h0]

theorem run_blank_1 (m : Machine) (hm : compatible fiveSlot m) :
    run m 1 blank = some bConfig := by
  have hA := (assigned_actions m hm).1
  simp only [run]
  change rawStep m blank = some bConfig
  unfold rawStep
  rw [show readSlot blank = a0 by rfl, hA]
  rfl

theorem run_blank_2 (m : Machine) (hm : compatible fiveSlot m) :
    run m 2 blank = some (cConfig 0) := by
  have hB := (assigned_actions m hm).2.1
  rw [run, run_blank_1 m hm]
  simp only [Option.bind_some]
  unfold rawStep
  rw [show readSlot bConfig = b0 by simp [readSlot, bConfig, blank, applyMove, b0], hB]
  simp [b0Action, bConfig_to_cConfig]

theorem run_cycle (m : Machine) (hm : compatible fiveSlot m) (k : Nat) :
    run m (2 + 3*k) blank = some (cConfig k) := by
  induction k with
  | zero => simpa using run_blank_2 m hm
  | succ k ih =>
      have hidx : 2 + 3*(k+1) = (2+3*k)+3 := by omega
      rw [hidx, run_compose m blank (2+3*k) 3, ih]
      exact run_c_3 m hm k

theorem run_exists (m : Machine) (hm : compatible fiveSlot m) (n : Nat) :
    ∃ c, run m n blank = some c := by
  by_cases hzero : n = 0
  · subst n
    exact ⟨blank, rfl⟩
  · by_cases hone : n = 1
    · subst n
      exact ⟨bConfig, run_blank_1 m hm⟩
    · have hn : 2 ≤ n := by omega
      let k := (n-2)/3
      let r := (n-2)%3
      have hdecomp : n = (2+3*k)+r := by
        dsimp [k, r]
        have hmod := Nat.mod_add_div (n-2) 3
        omega
      have hr : r = 0 ∨ r = 1 ∨ r = 2 := by
        dsimp [r]
        have hlt := Nat.mod_lt (n-2) (by decide : 0 < 3)
        omega
      rcases hr with h0 | h1 | h2
      · rw [h0] at hdecomp
        refine ⟨cConfig k, ?_⟩
        rw [hdecomp]
        simpa using run_cycle m hm k
      · rw [h1] at hdecomp
        refine ⟨dConfig k, ?_⟩
        rw [hdecomp]
        calc
          run m ((2+3*k)+1) blank =
              (run m (2+3*k) blank).bind (fun d => run m 1 d) :=
                run_compose m blank (2+3*k) 1
          _ = some (dConfig k) := by rw [run_cycle m hm k]; exact run_c_1 m hm k
      · rw [h2] at hdecomp
        refine ⟨eConfig k, ?_⟩
        rw [hdecomp]
        calc
          run m ((2+3*k)+2) blank =
              (run m (2+3*k) blank).bind (fun d => run m 2 d) :=
                run_compose m blank (2+3*k) 2
          _ = some (eConfig k) := by rw [run_cycle m hm k]; exact run_c_2 m hm k

theorem fiveSlot_never (m : Machine) (hm : compatible fiveSlot m) : NeverHalts m := by
  intro n
  obtain ⟨c, hc⟩ := run_exists m hm n
  simp [hc]

theorem fiveSlot_cover (bound : Nat) : Cover (DecidedBelow bound) fiveSlot := by
  apply Cover.leaf
  intro m hm
  exact Or.inl (fiveSlot_never m hm)

#print axioms fiveSlot_never
#print axioms fiveSlot_cover

end BB6Coverage.DirectFiveSlot

namespace BB6Coverage.DirectFiveSlot

theorem fiveSlot_is_p4_child : fiveSlot = refine p4 e0 e0Action := rfl

theorem p4_e0_unassigned : p4 e0 = none := by
  decide

theorem fiveSlot_parent_compatible (m : Machine)
    (hm : compatible fiveSlot m) : compatible p4 m := by
  have hchild : compatible (refine p4 e0 e0Action) m := by
    simpa [fiveSlot] using hm
  exact (compatible_refine_iff p4 m e0 p4_e0_unassigned e0Action).mp hchild |>.1

#print axioms fiveSlot_parent_compatible

end BB6Coverage.DirectFiveSlot
