import JFirstBranch
import Lean.Elab.Tactic.Omega

/-!
# Exact raw-time composition of consecutive high-3 J branches

This module composes the source-checked one-branch theorem
`BB429JFirstBranch.j_first_branch` through arbitrary consecutive cases
`w ≥ 2*u+3`.  Translation invariance is proved for the actual
`BB6Coverage.run` semantics, so the result concerns the raw six-state
machine and its original tape, not a separate simulator.
-/

namespace BB429High3Ladder

open BB6Coverage BB6Bubble BB429PhysicalFrontier BB429JPhysical

/-- Translate a complete two-sided tape configuration by an integer offset. -/
def shiftConfig (d : Int) (c : Config) : Config :=
  { state := c.state, head := c.head+d, tape := fun x => c.tape (x-d) }

theorem readSlot_shiftConfig (d : Int) (c : Config) :
    readSlot (shiftConfig d c) = readSlot c := by
  simp [readSlot, shiftConfig]

theorem shiftConfig_applyMove (d : Int) (c : Config) (t : Move) :
    shiftConfig d (applyMove c t) = applyMove (shiftConfig d c) t := by
  cases c with
  | mk state head tape =>
    cases t with
    | mk write right next =>
      simp only [shiftConfig, applyMove]
      congr 1
      · omega
      · funext x
        by_cases hx : x = head+d
        · subst x
          simp
        · have hx' : x-d ≠ head := by omega
          simp [hx, hx']

theorem rawStep_shiftConfig (m : Machine) (d : Int) (c : Config) :
    rawStep m (shiftConfig d c) = (rawStep m c).map (shiftConfig d) := by
  simp [rawStep, readSlot_shiftConfig, shiftConfig_applyMove, Function.comp_def]

theorem run_shiftConfig (m : Machine) (n : Nat) (d : Int) (c : Config) :
    run m n (shiftConfig d c) = (run m n c).map (shiftConfig d) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run, ih]
    cases h : run m n c with
    | none => simp
    | some d => simp [rawStep_shiftConfig]

theorem shiftConfig_comp (d e : Int) (c : Config) :
    shiftConfig d (shiftConfig e c) = shiftConfig (d+e) c := by
  cases c with
  | mk state head tape =>
    simp [shiftConfig, Int.add_comm, Int.add_left_comm, Int.sub_sub]

/-- The J-family configuration with its head at the origin. -/
def jConfig (u w : Nat) : Config :=
  { state := A, head := 0, tape := jTape u w }

/-- The source-checked first J branch, transported to any absolute head. -/
theorem j_first_branch_shift (u w : Nat) (d : Int)
    (hw : 2*u+3 ≤ w) :
    run target429 (4*u*u+10*u+27) (shiftConfig d (jConfig u w)) =
      some (shiftConfig (d+(2*(u:Int)+3))
        (jConfig (2*u+3) (w-(2*u+3)))) := by
  have hraw : run target429 (4*u*u+10*u+27) (jConfig u w) =
      some (Config.mk A (2*(u:Int)+3)
        (BB429JFirstBranch.jTapeAt (2*u+3) (w-(2*u+3)) (2*(u:Int)+3))) := by
    have hraw0 := BB429JFirstBranch.j_first_branch u w hw
    change run target429 (4*u*u+10*u+27) (jConfig u w) = _ at hraw0
    exact hraw0
  rw [run_shiftConfig, hraw]
  have hout :
      Config.mk A (2*(u:Int)+3)
        (BB429JFirstBranch.jTapeAt (2*u+3) (w-(2*u+3)) (2*(u:Int)+3)) =
      shiftConfig (2*(u:Int)+3) (jConfig (2*u+3) (w-(2*u+3))) := by
    change Config.mk A (2*(u:Int)+3)
        (BB429JFirstBranch.jTapeAt (2*u+3) (w-(2*u+3)) (2*(u:Int)+3)) =
      Config.mk A (0+(2*(u:Int)+3))
        (fun x => jTape (2*u+3) (w-(2*u+3)) (x-(2*(u:Int)+3)))
    rw [Config.mk.injEq]
    refine ⟨rfl, ?_, ?_⟩
    · simp
    · funext x
      simp [BB429JFirstBranch.jTapeAt]
  simp only [Option.map_some]
  rw [hout, shiftConfig_comp]

/-- Cumulative head displacement after k consecutive high-3 branches. -/
def branchShift : Nat → Nat → Nat
  | u, 0 => 0
  | u, k+1 => 2*u+3 + branchShift (2*u+3) k

/-- J parameter u after k consecutive high-3 branches. -/
def branchU : Nat → Nat → Nat
  | u, 0 => u
  | u, k+1 => branchU (2*u+3) k

/-- Exact primitive cost of one high-3 branch. -/
def branchCost (u : Nat) : Nat := 4*u*u+10*u+27

/-- Exact sum of primitive costs for k consecutive high-3 branches. -/
def branchCostSum : Nat → Nat → Nat
  | u, 0 => 0
  | u, k+1 => branchCost u + branchCostSum (2*u+3) k

theorem mul_two_mul (a x : Nat) : 2*a*(2*x) = 4*a*x := by
  have hc : 2*(2*a) = 4*a := by omega
  calc
    2*a*(2*x) = x*(2*(2*a)) := by simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    _ = x*(4*a) := by rw [hc]
    _ = 4*a*x := by simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

theorem mul_two_add_one (a x : Nat) : 2*a*(2*x+1) = 4*a*x+2*a := by
  rw [Nat.mul_add]
  calc
    2*a*(2*x) + 2*a*1 = 4*a*x+2*a := by rw [mul_two_mul]; simp

theorem branchU_closed (u k : Nat) :
    branchU u k = 2^k*(u+3)-3 := by
  induction k generalizing u with
  | zero => simp [branchU]
  | succ k ih =>
    rw [branchU, ih (2*u+3)]
    have hp : 2^(k+1) = 2^k*2 := Nat.pow_succ 2 k
    rw [hp]
    have hcoef : 2*u+3+3 = 2*(u+3) := by omega
    rw [hcoef]
    simp [Nat.mul_assoc]

theorem branchShift_closed (u k : Nat) :
    branchShift u k + 3*k = 2*(u+3)*(2^k-1) := by
  induction k generalizing u with
  | zero => simp [branchShift]
  | succ k ih =>
    rw [branchShift, Nat.mul_succ]
    have hp : 2^(k+1)-1 = 2*(2^k-1)+1 := by
      have hpow : 2^(k+1) = 2^k*2 := Nat.pow_succ 2 k
      have hpos : 1 ≤ 2^k := Nat.one_le_pow k 2 (by decide)
      omega
    rw [hp]
    have hB : 2*(2*u+6) = 4*(u+3) := by omega
    calc
      2*u+3 + branchShift (2*u+3) k + (3*k+3)
          = 2*(u+3) + (branchShift (2*u+3) k + 3*k) := by omega
      _ = 2*(u+3) + 2*(2*u+6)*(2^k-1) := by rw [ih]
      _ = 2*(u+3) + 4*(u+3)*(2^k-1) := by rw [hB]
      _ = 2*(u+3)*(2*(2^k-1)+1) := by
              rw [Nat.add_comm]
              exact (mul_two_add_one (u+3) (2^k-1)).symm

/--
For every k whose cumulative high-3 decrement fits inside w, the original
machine executes exactly the sum of the k one-branch primitive costs and
returns to the corresponding translated J configuration.
-/
theorem j_high3_ladder (u w k : Nat) (d : Int)
    (hw : branchShift u k ≤ w) :
    run target429 (branchCostSum u k) (shiftConfig d (jConfig u w)) =
      some (shiftConfig (d+(branchShift u k : Int))
        (jConfig (branchU u k) (w-branchShift u k))) := by
  induction k generalizing u w d with
  | zero => simp [branchCostSum, branchShift, branchU, run, jConfig, shiftConfig]
  | succ k ih =>
    have hD : branchShift u (k+1) = 2*u+3 + branchShift (2*u+3) k := rfl
    have hsum : 2*u+3 + branchShift (2*u+3) k ≤ w := by
      simpa [hD] using hw
    have hfirst : 2*u+3 ≤ w := by omega
    have hrest : branchShift (2*u+3) k ≤ w-(2*u+3) := by
      apply (Nat.le_sub_iff_add_le hfirst).2
      omega
    have hcost : branchCostSum u (k+1) =
        branchCost u + branchCostSum (2*u+3) k := rfl
    rw [hcost, BB6Bubble.run_add']
    rw [show branchCost u = 4*u*u+10*u+27 by rfl]
    rw [j_first_branch_shift u w d hfirst]
    simp only [Option.bind_some]
    rw [ih (2*u+3) (w-(2*u+3)) (d+(2*(u:Int)+3)) hrest]
    have hDcast : (branchShift u (k+1) : Int) =
        (2*u+3 : Nat) + (branchShift (2*u+3) k : Nat) := by
      exact congrArg (fun n : Nat => (n : Int)) hD
    have hhead : d + (2*(u:Int)+3) + (branchShift (2*u+3) k : Int) =
        d + (branchShift u (k+1) : Int) := by
      have hDcast' : (branchShift u (k+1) : Int) =
          (2*(u:Int)+3) + (branchShift (2*u+3) k : Int) := by
        simpa [Int.natCast_add, Int.natCast_mul] using hDcast
      omega
    have hU : branchU (2*u+3) k = branchU u (k+1) := rfl
    have htape : w-(2*u+3)-branchShift (2*u+3) k =
        w-branchShift u (k+1) := by
      rw [hD, Nat.sub_sub]
    rw [hhead, hU, htape]

#print axioms BB429High3Ladder.j_high3_ladder

end BB429High3Ladder
