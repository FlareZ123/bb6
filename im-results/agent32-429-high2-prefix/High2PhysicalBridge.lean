import High2Prefix
import JFirstBranch
import BB429DeltaPhysicalBridge
import Lean.Elab.Tactic.Omega

namespace BB429High2PhysicalBridge

open BB6Coverage BB6Bubble BB6BCFuture BB429PhysicalFrontier BB429JPhysical
open BB429JFirstBranch BB429PhysicalBridge BB429OddExcursion
open BB429SourceE1Return BB429High2Prefix BB429JuncHeadExcursion

private theorem tens_length (n : Nat) : (tens n).length = 2*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [tens, ih]; omega

private theorem ones_getD (n j : Nat) (hj : j<n) :
    (ones n).getD j false = true := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
      cases j with
      | zero => simp [ones]
      | succ j =>
          have hj' : j<n := by omega
          simpa [ones, List.replicate_succ] using ih j hj'

private theorem ones_getD_ge (n j : Nat) (hj : n≤j) :
    (ones n).getD j false = false := by
  induction n generalizing j with
  | zero => simp [ones]
  | succ n ih =>
      cases j with
      | zero => simp at hj
      | succ j =>
          have hj' : n≤j := by omega
          simpa [ones, List.replicate_succ] using ih j hj'

private theorem tens_getD (n j : Nat) (hj : j < 2*n) :
    (tens n).getD j false = (j % 2 == 0) := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
      cases j with
      | zero => simp [tens]
      | succ j =>
          cases j with
          | zero => simp [tens]
          | succ j =>
              have hj' : j < 2*n := by omega
              have hmod : (j+2)%2 = j%2 := by omega
              simpa [tens, hmod] using ih j hj'

private theorem getD_append_left (xs ys : List Bool) (j : Nat)
    (hj : j<xs.length) :
    (xs++ys).getD j false = xs.getD j false := by
  induction xs generalizing ys j with
  | nil => simp at hj
  | cons x xs ih =>
      cases j with
      | zero => simp
      | succ j =>
          have hj' : j<xs.length := by simp at hj; omega
          simpa using ih ys j hj'

private theorem getD_append_right (xs ys : List Bool) (j : Nat)
    (hj : xs.length≤j) :
    (xs++ys).getD j false = ys.getD (j-xs.length) false := by
  induction xs generalizing ys j with
  | nil => simp
  | cons x xs ih =>
      cases j with
      | zero => simp at hj
      | succ j =>
          have hj' : xs.length≤j := by simp at hj; omega
          simpa using ih ys j hj'

/-- To the right of the high-2 C/B sweep, the source tape is the two
    remaining ones followed by 01, with all later cells blank. -/
private theorem baseTape_high2_right (u : Nat) (x : Int)
    (hx : 2*(u:Int)+1≤x) :
    baseTape u (2*u+2) x =
      (if (x=2*(u:Int)+1 ∨ x=2*(u:Int)+2 ∨
           x=2*(u:Int)+3 ∨ x=2*(u:Int)+5) then true else false) := by
  have hz : ¬zeroTest (2*(u:Int)) x (2*u+3) := by
    unfold zeroTest
    omega
  have hn : ¬negFillTest u x := by
    unfold negFillTest
    omega
  have hj : jTape u (2*u+2) x =
      (if (x=2*(u:Int)+1 ∨ x=2*(u:Int)+2 ∨
           x=2*(u:Int)+3 ∨ x=2*(u:Int)+5) then true else false) := by
    have hmark : jMark u (2*u+2) x ↔
        x=2*(u:Int)+1 ∨ x=2*(u:Int)+2 ∨
          x=2*(u:Int)+3 ∨ x=2*(u:Int)+5 := by
      unfold jMark jHole
      omega
    simp [jTape, hmark]
  simp [baseTape, zeroPaint, hz, negFill, hn, hj]

/-- The exact physical configuration emitted by the C/B sweep in
    Agent1's j_c_sweep theorem, at w=2u+2. -/
def high2SweepConfig (u : Nat) : Config :=
  { state := C
    head := 2*(u:Int)+1
    tape := cbPaint (setupTape (f0Tape u (2*u+2)) (-2*(u:Int)-7))
      (-2*(u:Int)-3) (2*u+2) }

/-- The C/B sweep endpoint has precisely the finite zipper shape used by
    the high-2 source macro. The proof checks every tape cell, including
    the six-cell setup fringe and the blank right tail. -/
theorem j_c_sweep_high2_rep (u : Nat) :
    Represents (high2SweepStart u) (high2SweepConfig u) := by
  change C.val = 2 ∧
    cbPaint (setupTape (f0Tape u (2*u+2)) (-2*(u:Int)-7))
      (-2*(u:Int)-3) (2*u+2) (2*(u:Int)+1) = true ∧
    (∀ j : Nat,
      cbPaint (setupTape (f0Tape u (2*u+2)) (-2*(u:Int)-7))
        (-2*(u:Int)-3) (2*u+2)
        (2*(u:Int)+1-((j:Int)+1)) =
        (tens (2*u+2) ++ ones 6).getD j false) ∧
    (∀ j : Nat,
      cbPaint (setupTape (f0Tape u (2*u+2)) (-2*(u:Int)-7))
        (-2*(u:Int)-3) (2*u+2)
        (2*(u:Int)+1+((j:Int)+1)) =
        (ones 2 ++ [false,true]).getD j false)
  refine ⟨rfl, ?_, ?_, ?_⟩
  · have hcb : (-2*(u:Int)-3)+2*((2*u+2):Int) ≤ 2*(u:Int)+1 := by omega
    rw [cbPaint_right _ _ _ _ hcb]
    rw [setupTape_above _ _ _ (by omega)]
    rw [f0Tape_neq u (2*u+2) _ (by omega)]
    rw [baseTape_high2_right u _ (by omega)]
    simp
  · intro j
    let k : Nat := 2*u+2
    let h : Int := -2*(u:Int)-3
    let x : Int := 2*(u:Int)+1-((j:Int)+1)
    change cbPaint (setupTape (f0Tape u (2*u+2)) (-2*(u:Int)-7))
      (-2*(u:Int)-3) (2*u+2) x =
      (tens (2*u+2) ++ ones 6).getD j false
    by_cases hj : j < 2*k
    · have hlo : h≤x := by dsimp [h, x, k]; omega
      have hhi : x<h+2*(k:Int) := by dsimp [h, x, k]; omega
      by_cases he : j%2=0
      · have hodd : (x-h)%2=1 := by dsimp [x, h, k]; omega
        rw [cbPaint_odd _ _ _ _ hlo hhi hodd]
        rw [getD_append_left _ _ j (by rw [tens_length]; exact hj)]
        rw [tens_getD _ _ hj]
        simp [he]
      · have heven : (x-h)%2=0 := by dsimp [x, h, k]; omega
        rw [cbPaint_even _ _ _ _ hlo hhi heven]
        rw [getD_append_left _ _ j (by rw [tens_length]; exact hj)]
        rw [tens_getD _ _ hj]
        simp [he]
    · have hjk : 2*k≤j := by omega
      let i := j-2*k
      have hx : x = h - ((i:Int)+1) := by dsimp [x, h, k, i]; omega
      rw [hx]
      rw [cbPaint_left _ _ _ _ (by dsimp [h]; omega)]
      by_cases hi : i<6
      · have hset :
            setupTape (f0Tape u (2*u+2)) (-2*(u:Int)-7)
              (h-((i:Int)+1)) = true := by
          apply setupTape_window
          dsimp [h]
          omega
        rw [hset]
        rw [getD_append_right _ _ j (by rw [tens_length]; exact hjk)]
        rw [tens_length]
        have hidx : j-2*k=i := rfl
        rw [hidx]
        exact (ones_getD 6 i hi).symm
      · have hset :
            setupTape (f0Tape u (2*u+2)) (-2*(u:Int)-7)
              (h-((i:Int)+1)) = f0Tape u (2*u+2) (h-((i:Int)+1)) := by
          apply setupTape_below
          dsimp [h]
          omega
        rw [hset, f0Tape_neq u (2*u+2) _ (by dsimp [h]; omega)]
        rw [baseTape_left_blank u (2*u+2) _ (by dsimp [h]; omega)]
        rw [getD_append_right _ _ j (by rw [tens_length]; exact hjk)]
        rw [tens_length]
        have hidx : j-2*k=i := rfl
        rw [hidx]
        exact (ones_getD_ge 6 i (by omega)).symm
  · intro j
    let x : Int := 2*(u:Int)+1+((j:Int)+1)
    change cbPaint (setupTape (f0Tape u (2*u+2)) (-2*(u:Int)-7))
      (-2*(u:Int)-3) (2*u+2) x =
      (ones 2 ++ [false,true]).getD j false
    have hcb : (-2*(u:Int)-3)+2*((2*u+2):Int) ≤ x := by
      dsimp [x]
      omega
    rw [cbPaint_right _ _ _ _ hcb]
    rw [setupTape_above _ _ _ (by dsimp [x]; omega)]
    rw [f0Tape_neq u (2*u+2) x (by dsimp [x]; omega)]
    rw [baseTape_high2_right u x (by dsimp [x]; omega)]
    have hx0 : x ≠ 2*(u:Int)+1 := by dsimp [x]; omega
    have hx1 : x = 2*(u:Int)+2 ↔ j=0 := by dsimp [x]; omega
    have hx2 : x = 2*(u:Int)+3 ↔ j=1 := by dsimp [x]; omega
    have hx3 : x = 2*(u:Int)+5 ↔ j=3 := by dsimp [x]; omega
    cases j with
    | zero => simp [hx0, hx1, hx2, hx3, ones]
    | succ j =>
        cases j with
        | zero => simp [hx0, hx1, hx2, hx3, ones]
        | succ j =>
            cases j with
            | zero => simp [hx0, hx1, hx2, hx3, ones]
            | succ j =>
                cases j with
                | zero => simp [hx0, hx1, hx2, hx3, ones]
                | succ j => simp [hx0, hx1, hx2, hx3, ones]

/-- The source-verified high-2 zipper macro lifts to the original #429
    transition table from the authentic J(u,2u+2) raw configuration. -/
def high2SuffixTime (u : Nat) : Nat :=
  21 + (crossTime (2*(u+1))+1 + (12+2*(2*(u+1))) +
    (2*(2*(u+1)+2)+6))

theorem j_high2_to_midA_raw (u : Nat) :
    ∃ c', BB6Coverage.run target429 (4*u*u+32*u+132)
      {state:=A,head:=0,tape:=jTape u (2*u+2)} = some c' ∧
      Represents (midA2 (2*u+4) 1) c' ∧ c'.head = 2*(u:Int)+6 := by
  let c0 : Config := {state:=A,head:=0,tape:=jTape u (2*u+2)}
  have hprefix :
      BB6Coverage.run target429 (4*u*u+10*u+25) c0 =
        some (high2SweepConfig u) := by
    simpa [c0, high2SweepConfig] using
      (BB429JFirstBranch.j_c_sweep u (2*u+2) (by omega))
  obtain ⟨c', hrun, hrep, hhead⟩ :=
    BB429DeltaPhysicalBridge.source_runWithDelta_rep
      (high2SuffixTime u) (high2SweepStart u) (high2SweepConfig u)
      (j_c_sweep_high2_rep u) (midA2 (2*u+4) 1) 5
      (by simpa [high2SuffixTime] using
        (BB429High2Prefix.high2_to_midA u))
  have htotal :
      BB6Coverage.run target429 ((4*u*u+10*u+25)+high2SuffixTime u) c0 =
        some c' := by
    rw [BB6Bubble.run_add' target429 (4*u*u+10*u+25)
      (high2SuffixTime u) c0, hprefix]
    simp only [Option.bind_some]
    exact hrun
  have htime :
      (4*u*u+10*u+25)+high2SuffixTime u = 4*u*u+32*u+132 := by
    rw [high2SuffixTime, BB429SourceE1Return.crossTime_even]
    omega
  have hhead' : c'.head = 2*(u:Int)+6 := by
    have hh := hhead
    simp [high2SweepConfig] at hh
    omega
  exact ⟨c', by simpa [htime] using htotal, hrep, hhead'⟩

#print axioms j_c_sweep_high2_rep
#print axioms j_high2_to_midA_raw

end BB429High2PhysicalBridge
