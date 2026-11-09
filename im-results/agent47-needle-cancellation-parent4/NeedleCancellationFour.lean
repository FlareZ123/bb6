import NeedleCancelMod35
import CancellationTerminalConstructive
import SpaceNeedleClosed
import Lean.Elab.Tactic.Omega

namespace BB6.Agent47NeedleCancellationFour

open BB6.Agent48.SpaceNeedle
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open NeedleCancelMod35

/-- Identify the self-contained geometric polynomial with the
    source-checked cancellation construction of Agent 20. -/
theorem P_eq_geo (A r:Nat) :
    CancellationNat.P A r=(A-3)*geo (A*A) 9 r := by
  induction r with
  | zero => simp [CancellationNat.P,geo]
  | succ r ih =>
      simp only [CancellationNat.P, geo]
      rw [ih]
      simp [Nat.mul_add, Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]

theorem valuationA_eq_v_succ (r:Nat) :
    CancellationGap.valuationA r=v r+1 := by
  have hp:9^r%2=1:=by
    rw [Nat.pow_mod]
    simp
  have hv:2*v r=9^r+3:=by
    dsimp [v]
    omega
  have ha:=CancellationGap.valuationA_double r
  omega

theorem sourceB_eq_P (r:Nat):
    sourceB r=2^(v r)*CancellationNat.P (2^(CancellationGap.valuationA r)) r := by
  rw [valuationA_eq_v_succ, P_eq_geo]
  have hp : (2^(v r+1))^2 = 2^(v r+1)*2^(v r+1) := by
    rw [show (2:Nat)=1+1 by decide, Nat.pow_succ]
    simp
  unfold sourceB xb
  rw [hp]
  simp only [Nat.mul_assoc]

theorem geo_pos (a b r:Nat) (hb:1≤b) (hr:1≤r) :
    1≤geo a b r := by
  cases r with
  | zero => omega
  | succ r =>
      simp only [geo]
      have hp : 1≤b^r := Nat.pow_pos (by omega)
      omega

theorem sourceB_ge55 (r:Nat) (hr:1≤r) : 55≤sourceB r := by
  have hval : 6≤v r := by
    have hp : 9≤9^r := by
      have h0 : 9^1 ≤9^r := Nat.pow_le_pow_right (by decide) hr
      simpa using h0
    dsimp [v]
    omega
  have hp : (2:Nat)^6 ≤2^(v r) := Nat.pow_le_pow_right (by decide) hval
  have hX : 2^7 ≤ xb r := by
    dsimp [xb]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:Nat))
      (by omega : 7≤v r+1)
  have hg : 1 ≤ geo ((xb r)^2) 9 r :=
    geo_pos ((xb r)^2) 9 r (by decide) hr
  have hdiff : 125 ≤ xb r-3 := by omega
  have hproduct : 64*125 ≤ 2^(v r)*(xb r-3) :=
    Nat.mul_le_mul hp hdiff
  have hproduct2 :
      (64*125)*1 ≤ (2^(v r)*(xb r-3))*geo ((xb r)^2) 9 r :=
    Nat.mul_le_mul hproduct hg
  dsimp [sourceB]
  omega

def parentQ4 (t:Nat) : Nat := (sourceB (3*t+1)-55)/35

/-- Every r=3t+1 member has an exact legal valuation-four
    arithmetic predecessor, with no bound on t. -/
theorem sourceB_parent4 (t:Nat) :
    sourceB (3*t+1)=35*parentQ4 t+55 := by
  have hm : sourceB (3*t+1)%35=20 := sourceB_mod35 t
  have hsize : 55≤sourceB (3*t+1) :=
    sourceB_ge55 (3*t+1) (by omega)
  dsimp [parentQ4]
  omega

/-- The polynomial target is exactly Agent 20's original-source
    cancellation feeder, represented by the genuine high-level counter. -/
theorem sourceB_is_original_feeder (r:Nat) (hr:1≤r) :
    oddTower (CancellationConstructive.feederQ r)
        (CancellationTerminalConstructive.feederV r) + 2 =
      sourceB r := by
  rw [oddTower_factor]
  have hv : CancellationTerminalConstructive.feederV r = v r := by
    unfold CancellationTerminalConstructive.feederV
    rw [valuationA_eq_v_succ r]
    omega
  rw [hv, sourceB_eq_P]
  rw [CancellationConstructive.feederQ_spec r hr]

/-- Infinite exact original-source reverse edges entering the cancellation
    terminal feeders, with inverse valuation four at every r=3t+1.
    These predecessor states have not been proved blank-root reachable. -/
theorem infinite_cancellation_four_parent (t:Nat) :
    ∃ q:Nat,
      highLevelNext (.N (oddTower q 4)) =
        some (.N (oddTower
          (CancellationConstructive.feederQ (3*t+1))
          (CancellationTerminalConstructive.feederV (3*t+1)))) := by
  let r:=3*t+1
  let q:=parentQ4 t
  have hfeed : oddTower (CancellationConstructive.feederQ r)
      (CancellationTerminalConstructive.feederV r)+2=sourceB r :=
    sourceB_is_original_feeder r (by omega)
  have hb : sourceB r=35*q+55 := by
    simpa [r,q] using sourceB_parent4 t
  have hq4 : oddTower q 4+2=16*(2*q+3) := by
    simpa using oddTower_factor q 4
  refine ⟨q, (highLevelNext_iff_oddTower
    (oddTower q 4)
    (oddTower (CancellationConstructive.feederQ r)
      (CancellationTerminalConstructive.feederV r))).mpr ?_⟩
  refine ⟨q,4,rfl,?_⟩
  omega

#print axioms sourceB_parent4
#print axioms sourceB_is_original_feeder
#print axioms infinite_cancellation_four_parent
end BB6.Agent47NeedleCancellationFour
