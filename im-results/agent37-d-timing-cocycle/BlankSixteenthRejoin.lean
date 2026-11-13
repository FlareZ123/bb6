import Lean.Elab.Tactic.Omega
import BlankFifteenthRejoin
import DRegularFast

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

/-- Smaller 3-adic blocks reduce the cost of exact long-prefix evaluation.
    This is the same source-proved shift algorithm as DRegularFast, with
    64-section blocks instead of 512. -/
namespace BB6.Agent2Fast64

open DRegular BB6.DRegularShift BB6.DRegularFast

def blockSize : Nat := 64

def fastRunBlocks : Nat → L → Option L
  | 0, s => some s
  | n+1, s =>
    match run blockSize (baseState s blockSize) with
    | none => none
    | some t =>
      fastRunBlocks n (shiftNat t (8^blockSize * liftParam s blockSize))

theorem fastRunBlocks_correct (n : Nat) :
    ∀ (s : L), Canon s →
      run (blockSize*n) s = fastRunBlocks n s := by
  induction n with
  | zero =>
    intro s hs
    simp [fastRunBlocks, run]
  | succ n ih =>
    intro s hs
    let base := baseState s blockSize
    let p := liftParam s blockSize
    have hmul : blockSize*(n+1) = blockSize + blockSize*n := by
      simp [blockSize, Nat.mul_add]
      omega
    have hblock := run_block s blockSize hs
    rw [hmul, run_add, hblock]
    cases hr : run blockSize base with
    | none =>
      simp [fastRunBlocks, base, hr]
    | some t =>
      let t' := shiftNat t (8^blockSize*p)
      have hb : run blockSize s = some t' := by
        rw [hblock, hr]
        rfl
      have ht' : Canon t' := run_canon blockSize s t' hs hb
      have hright : fastRunBlocks (n+1) s = fastRunBlocks n t' := by
        simp [fastRunBlocks, base, p, hr, t']
      rw [hright]
      simpa [t'] using (ih t' ht')

def fastRun (n : Nat) (s : L) : Option L :=
  (fastRunBlocks (n / blockSize) s).bind (run (n % blockSize))

theorem fastRun_correct (n : Nat) (s : L) (hs : Canon s) :
    run n s = fastRun n s := by
  have hdiv : n = blockSize*(n/blockSize)+n%blockSize := by
    calc
      n = n%blockSize + blockSize*(n/blockSize) :=
        (Nat.mod_add_div n blockSize).symm
      _ = blockSize*(n/blockSize)+n%blockSize := Nat.add_comm _ _
  calc
    run n s = run (blockSize*(n/blockSize)+n%blockSize) s :=
      congrArg (fun m => run m s) hdiv
    _ = (run (blockSize*(n/blockSize)) s).bind (run (n%blockSize)) :=
      run_add (blockSize*(n/blockSize)) (n%blockSize) s
    _ = (fastRunBlocks (n/blockSize) s).bind (run (n%blockSize)) := by
      rw [fastRunBlocks_correct (n/blockSize) s hs]
    _ = fastRun n s := rfl

end BB6.Agent2Fast64

namespace BB6.Agent2SixteenthRoot

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

def seed16 : DRegular.L :=
  ⟨64*BB6.Agent2FifteenthRoot.t15+33,1,5⟩

def terminal2077 : DRegular.L :=
  (DRegular.run 2077 seed16).getD ⟨9,0,0⟩

def t16 : Nat := (terminal2077.a-4)/9

/-- Exact DRegular computation after the fifteenth E/B reentry.
    Evaluate the 2,077-step prefix through 64-step 3-adic blocks;
    this avoids normalizing the full huge unary seed at every transition. -/
theorem terminal2077_exact :
    DRegular.run 2077 seed16 = some ⟨9*t16+4,5,1⟩ := by
  have hcanon : DRegular.Canon seed16 := by decide
  rw [BB6.Agent2Fast64.fastRun_correct 2077 seed16 hcanon]
  decide

def exception16Time : Nat :=
  BB6.Agent2FifteenthRoot.reentry15Time +
    DRegular.accumulated 2077 seed16

theorem blank_sixteenth_exception :
    ObsEq (run exception16Time blank)
      (DRegularSource.sourceSection ⟨9*t16+4,5,1⟩) := by
  apply BB6.Agent25RootChain.extend_regular blank
    BB6.Agent2FifteenthRoot.reentry15Time
    2077 seed16 ⟨9*t16+4,5,1⟩
  · constructor
    · change 64*BB6.Agent2FifteenthRoot.t15+33 ≥ 2
      omega
    · left
      change (1:Nat) ≠ 0
      omega
  · exact terminal2077_exact
  · exact BB6.Agent2FifteenthRoot.blank_fifteenth_reentry

def packet16Time : Nat :=
  BB6.Agent32EAll.duration (3*t16) 4 +
    BB6.Agent25BGeneral.bCost t16

def reentry16Time : Nat := exception16Time+packet16Time

theorem blank_sixteenth_reentry :
    ObsEq (run reentry16Time blank)
      (DRegularSource.sourceSection ⟨64*t16+27,1,5⟩) := by
  exact source_chain exception16Time packet16Time blank
    (DRegularSource.sourceSection ⟨9*t16+4,5,1⟩)
    (DRegularSource.sourceSection ⟨64*t16+27,1,5⟩)
    blank_sixteenth_exception
    (by simpa only [packet16Time] using
      (BB6.Agent25BGeneral.exceptional_EB_general t16 3))

#print axioms terminal2077_exact
#print axioms blank_sixteenth_exception
#print axioms blank_sixteenth_reentry

end BB6.Agent2SixteenthRoot
