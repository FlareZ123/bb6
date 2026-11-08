import DyadicGap
import TwoRunModel

namespace BB6.Agent43TwoRun

private theorem nat_equiv_t0
    (n r : Nat)
    (h : (245:Int)*(2:Int)^n =
      ((112*n+336*r+400:Int)*(8:Int)^r)+(35*n+90)) :
    245*(2:Nat)^n = (112*n+336*r+400)*(8:Nat)^r+(35*n+90) := by
  have hcast :
      (↑(245*(2:Nat)^n):Int) =
      ↑((112*n+336*r+400)*(8:Nat)^r+(35*n+90):Nat) := by
    simpa [Int.natCast_mul, Int.natCast_add, Int.natCast_pow] using h
  exact Int.ofNat_inj.mp hcast

private theorem nat_equiv_t1
    (n r : Nat)
    (h : (147:Int)*(2:Int)^n =
      ((224*n+672*r+1024:Int)*(8:Int)^r)+(21*n+54)) :
    147*(2:Nat)^n = (224*n+672*r+1024)*(8:Nat)^r+(21*n+54) := by
  have hcast :
      (↑(147*(2:Nat)^n):Int) =
      ↑((224*n+672*r+1024)*(8:Nat)^r+(21*n+54):Nat) := by
    simpa [Int.natCast_mul, Int.natCast_add, Int.natCast_pow] using h
  exact Int.ofNat_inj.mp hcast

/-- A single depth-zero inverse transition from the seed, followed by an
arbitrary count of depth-two transitions, cannot land on the shifted wall. -/
theorem no_root_zero_then_twos_wall
    (n r : Nat) (hn : 14 ≤ n) (Wend Bend : Int)
    (h : TwoRun ((2:Int)^n) (7*(2:Int)^n+3*n+10) ((n:Int)+7) r Wend Bend)
    (hw : Wend = 12*(2:Int)^n) : False := by
  let P : Int := (2:Int)^n
  let N : Int := n
  have hcost := run_cost P (7*P+3*N+10) (N+7) Wend Bend r h
  have henergy := run_energy P (7*P+3*N+10) (N+7) Wend Bend r h
  have hI0 : I P (7*P+3*N+10) (N+7) = -245*P+35*N+90 := by
    unfold I
    omega
  have hIE : I P Wend Bend = -(112*N+336*(r:Int)+400) := by
    rw [hw, hcost]
    unfold I
    omega
  rw [hI0,hIE] at henergy
  have hEq : (245:Int)*P =
      (112*N+336*(r:Int)+400)*(8:Int)^r+(35*N+90) := by
    rw [Int.mul_neg] at henergy
    rw [Int.mul_comm ((8:Int)^r) (112*N+336*(r:Int)+400)] at henergy
    omega
  have hEqNat := nat_equiv_t0 n r (by simpa [P,N] using hEq)
  exact no_zero_then_twos n r hn hEqNat

/-- A single depth-one inverse transition from the seed, followed by an
arbitrary count of depth-two transitions, cannot land on the shifted wall. -/
theorem no_root_one_then_twos_wall
    (n r : Nat) (hn : 14 ≤ n) (Wstart Wend Bend : Int)
    (hstart : 2*Wstart = 21*(2:Int)^n+5*(n:Int)+22)
    (h : TwoRun ((2:Int)^n) Wstart ((n:Int)+8) r Wend Bend)
    (hw : Wend = 12*(2:Int)^n) : False := by
  let P : Int := (2:Int)^n
  let N : Int := n
  have hcost := run_cost P Wstart (N+8) Wend Bend r h
  have henergy := run_energy P Wstart (N+8) Wend Bend r h
  have hI0 : 2*I P Wstart (N+8) = -147*P+21*N+54 := by
    unfold I
    omega
  have hIE : I P Wend Bend = -(112*N+336*(r:Int)+512) := by
    rw [hw,hcost]
    unfold I
    omega
  rw [hIE] at henergy
  have hE2 : 2*I P Wstart (N+8) =
      -((224*N+672*(r:Int)+1024)*(8:Int)^r) := by
    rw [Int.mul_neg] at henergy
    have heqComm :
      2*((8:Int)^r*(112*N+336*(r:Int)+512)) =
      (224*N+672*(r:Int)+1024)*(8:Int)^r := by
      calc
        _ = (2*(112*N+336*(r:Int)+512))*(8:Int)^r := by ac_rfl
        _ = _ := by
          have hc : 2*(112*N+336*(r:Int)+512) =
              224*N+672*(r:Int)+1024 := by omega
          rw [hc]
    omega
  have hEq : (147:Int)*P =
      (224*N+672*(r:Int)+1024)*(8:Int)^r+(21*N+54) := by omega
  have hEqNat := nat_equiv_t1 n r (by simpa [P,N] using hEq)
  exact no_one_then_twos n r hn hEqNat

#print axioms BB6.Agent43TwoRun.no_root_zero_then_twos_wall
#print axioms BB6.Agent43TwoRun.no_root_one_then_twos_wall
end BB6.Agent43TwoRun