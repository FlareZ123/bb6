import SheepOddInverse
import SheepValuationComplete

namespace GeneralVal
open SheepOddInverse
open SheepValuationComplete

/-- Any generic even source at prescribed valuation has an affine odd-slope output. -/
theorem generic_formula (a w : Nat) (hw : 2≤w) :
    Step (2^a*(2*w+1)) ((2^(a+1)+1)*w+2^a+a) := by
  have hu : (2*w+1)%2=1 := by omega
  have hlarge : 5≤2*w+1 := by omega
  have h := Step.generic a (2*w+1) hu hlarge
  have heq : 2^a*(2*w+1)+a+((2*w+1)-1)/2 =
      (2^(a+1)+1)*w+2^a+a := by
    have hwdiv : ((2*w+1)-1)/2=w := by omega
    rw [hwdiv, Nat.pow_succ]
    simp only [Nat.mul_add, Nat.add_mul]
    ac_rfl
  rw [heq] at h
  exact h

/-- Every positive valuation a has one genuine immediate-even generic successor
    of every positive target valuation b. -/
theorem complete_valuation_graph (a b : Nat) (_ha : 1≤a) (hb : 1≤b) :
    ∃ w v, 2≤w ∧ v%2=1 ∧ Step (2^a*(2*w+1)) (2^b*v) := by
  let c := 2^(a+1)+1
  let d := 2^a+a
  let M := 2^(b+1)
  let w0 := solve (b+1) c d (2^b)
  have hc : c%2=1 := by
    dsimp [c]
    rw [Nat.pow_succ]
    omega
  have hsol : (c*w0+d)%M=(2^b)%M :=
    solve_correct (b+1) c d (2^b) hc
  let w:=w0+M
  have hmge : 2≤M := by
    dsimp [M]
    have hpow := Nat.pow_le_pow_right (n:=2) (by decide)
      (show 1≤b+1 by omega)
    simpa only [show (2:Nat)^1=2 by decide] using hpow
  have hw:2≤w := by dsimp [w]; omega
  let y:=c*w+d
  have hshift : y=(c*w0+d)+M*c := by
    dsimp [y,w]
    rw [Nat.mul_add]
    ac_rfl
  have hy_mod : y%M=(2^b)%M := by
    rw [hshift, mod_add_multiple]
    exact hsol
  have hbpow : 2^b<M := by
    dsimp [M]
    rw [Nat.pow_succ]
    have hp:0<2^b:=Nat.pow_pos (by decide)
    omega
  have hy_mod' : y%M=2^b := by
    rw [Nat.mod_eq_of_lt hbpow] at hy_mod
    exact hy_mod
  let v:=2*(y/M)+1
  have hv : v%2=1 := by dsimp [v]; omega
  have hpower : 2^(b+1)=2^b*2 := by rw [Nat.pow_succ]
  have hy : y=2^b*v := by
    calc
      y = y%M +M*(y/M) := (Nat.mod_add_div y M).symm
      _ = 2^b + (2^b*2)*(y/M) := by rw [hy_mod']; simp only [M,hpower]
      _ = 2^b*v := by dsimp [v]; rw [Nat.mul_add]; ac_rfl
  refine ⟨w,v,hw,hv,?_⟩
  have hstep : Step (2^a*(2*w+1)) y := by
    simpa only [y,c,d,Nat.add_assoc] using generic_formula a w hw
  rw [hy] at hstep
  exact hstep

#print axioms complete_valuation_graph
end GeneralVal
