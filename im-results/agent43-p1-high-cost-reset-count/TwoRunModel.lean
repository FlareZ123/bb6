import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent43TwoRun

/-- Affine wall coordinate W and accumulated-cost coordinate B. All steps
are exact integer identities obtained from a depth-two inverse edge. -/
inductive TwoRun (P : Int) : Int → Int → Nat → Int → Int → Prop where
  | done (W B : Int) : TwoRun P W B 0 W B
  | step (W B W1 B1 W2 : Int) (r : Nat)
      (prior : TwoRun P W B r W1 B1)
      (stepEquation : 8*W2 = W1+84*P+16*B1) :
      TwoRun P W B (r+1) W2 (B1+3)

def I (P W B : Int) : Int := 49*W-588*P-112*B+384

private theorem energy_step (P W B W2 : Int)
    (h : 8*W2 = W+84*P+16*B) :
    I P W B = 8*I P W2 (B+3) := by
  unfold I
  omega

/-- Depth-two runs divide the affine 2-adic defect exactly by 8^r. -/
theorem run_energy (P W B W' B' : Int) (r : Nat)
    (h : TwoRun P W B r W' B') :
    I P W B = (8:Int)^r * I P W' B' := by
  induction h with
  | done => simp
  | step W1 B1 W2 r prior hstep ih =>
    have hs := energy_step P W1 B1 W2 hstep
    calc
      I P W B = (8:Int)^r * I P W1 B1 := ih
      _ = (8:Int)^r * (8*I P W2 (B1+3)) := by rw [hs]
      _ = (8:Int)^(r+1) * I P W2 (B1+3) := by
        rw [Int.pow_succ]
        ac_rfl

theorem run_cost (P W B W' B' : Int) (r : Nat)
    (h : TwoRun P W B r W' B') :
    B'=B+3*(r:Int) := by
  induction h with
  | done => simp
  | step W1 B1 W2 r prior hstep ih =>
    omega

end BB6.Agent43TwoRun