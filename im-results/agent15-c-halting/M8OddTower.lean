import M8OddDeep
import Lean.Elab.Tactic.Omega
namespace BB6.Agent15Research
open BB6.Agent29Depth

def towerSum (B : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => B*towerSum B n+1

def towerX (m r : Nat) : Nat := allOddB m^r
def towerS (m r : Nat) : Nat := towerSum (allOddB m) r
def towerR (m r : Nat) : Nat :=
  3*(allOddQ m-1)*towerS m r+1
def towerIndex (m r t : Nat) : Nat :=
  towerR m r*(m+1)+towerX m r*deepTail m t+3*(towerS m r-1)
def towerK (m r t : Nat) : Nat :=
  3*towerX m r*deepMass m t-2

theorem towerSum_nonzero (B r : Nat) (hr : 1≤r) :
    1≤towerSum B r := by
  cases r with
  | zero => omega
  | succ r =>
      simp only [towerSum]
      omega

theorem towerX_geom (m r : Nat) :
    3*allOddQ m*towerS m r+1=towerX m r := by
  let Q := allOddQ m
  let B := allOddB m
  have hB : B=3*Q+1 := allOdd_BQ m
  induction r with
  | zero => rfl
  | succ r ih =>
      have hS : towerS m (r+1)=B*towerS m r+1 := rfl
      have hX : towerX m (r+1)=B*towerX m r := by
        dsimp [towerX,B]
        rw [Nat.pow_succ]
        ac_rfl
      rw [hS,hX]
      calc
        3*Q*(B*towerS m r+1)+1
          = B*(3*Q*towerS m r+1) := by
            rw [hB]
            simp only [Nat.mul_add,Nat.add_mul,Nat.one_mul]
            ac_rfl
        _=B*towerX m r := by rw [ih]

private theorem towerR_plus (m r : Nat) (hr : 1≤r) :
    towerR m r+3*towerS m r=towerX m r := by
  let Q := allOddQ m
  let S := towerS m r
  have hQ4 : Q%4=1 := by
    dsimp [Q,allOddQ]
    exact m8Geom4_mod_four (m+1) (by omega)
  have hQpos : 1≤Q := by omega
  have hQsub : Q-1+1=Q := by omega
  have hX := towerX_geom m r
  dsimp [towerR]
  calc
    3*(Q-1)*S+1+3*S=3*(Q-1+1)*S+1 := by
      simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul]
      ac_rfl
    _=3*Q*S+1 := by rw [hQsub]
    _=towerX m r := hX

theorem tower_stopping_algebra (m r t : Nat) (hr : 1≤r) :
    3*towerX m r*deepMass m t+towerIndex m r t+3*m+3 =
      allOddB m*(towerIndex m r t+3) := by
  let B := allOddB m
  let Q := allOddQ m
  let S := towerS m r
  let X := towerX m r
  let R := towerR m r
  let T := deepTail m t
  let N := deepMass m t
  let J := towerIndex m r t
  have hQ4 : Q%4=1 := by
    dsimp [Q,allOddQ]
    exact m8Geom4_mod_four (m+1) (by omega)
  have hQpos : 1≤Q := by omega
  have hSpos : 1≤S := towerSum_nonzero B r hr
  have hSsub : S-1+1=S := by omega
  have hQsub : Q-1+1=Q := by omega
  have hB : B=3*Q+1 := allOdd_BQ m
  have hRS : R+3*S=X := towerR_plus m r hr
  have hX : X=3*Q*S+1 := (towerX_geom m r).symm
  have hJ : J+3+3*m*S=X*(m+T+1) := by
    have hmul : R*(m+1)+3*S*(m+1)=X*(m+1) := by
      calc
        R*(m+1)+3*S*(m+1)=(R+3*S)*(m+1) :=
          (Nat.add_mul R (3*S) (m+1)).symm
        _=X*(m+1) := by rw [hRS]
    have hss : 3*(S-1)+3=3*S := by omega
    calc
      J+3+3*m*S = R*(m+1)+3*S*(m+1)+X*T := by
        change (R*(m+1)+X*T+3*(S-1))+3+3*m*S = R*(m+1)+3*S*(m+1)+X*T
        have hprod : 3*S*(m+1)=3*m*S+3*S := by
          simp only [Nat.mul_add,Nat.mul_one]
          ac_rfl
        omega
      _=X*(m+1)+X*T := by rw [hmul]
      _=X*(m+T+1) := by
        rw [show m+T+1=(m+1)+T by omega]
        simp only [Nat.mul_add]
  have hN : N+m=Q*(m+T+1) := by
    change (Q-1)*m+Q*(T+1)+m=Q*(m+T+1)
    calc
      (Q-1)*m+Q*(T+1)+m=(Q-1+1)*m+Q*(T+1) := by
        simp only [Nat.add_mul,Nat.one_mul]
        ac_rfl
      _=Q*(m+T+1) := by
        rw [hQsub,show m+T+1=m+(T+1) by omega]
        simp only [Nat.mul_add]
  have hQJ : Q*(J+3)=X*N+m := by
    have hp : Q*(J+3)+3*Q*m*S=X*(N+m) := by
      calc
        Q*(J+3)+3*Q*m*S=Q*(J+3+3*m*S) := by
          simp only [Nat.mul_add,Nat.mul_assoc]
          ac_rfl
        _=Q*(X*(m+T+1)) := by rw [hJ]
        _=X*(Q*(m+T+1)) := by ac_rfl
        _=X*(N+m) := by rw [hN]
    have hh : X*(N+m)=X*N+3*Q*m*S+m := by
      rw [hX]
      simp only [Nat.mul_add,Nat.add_mul,Nat.one_mul]
      ac_rfl
    rw [hh] at hp
    omega
  have hBbase : B*(J+3)=3*Q*(J+3)+(J+3) := by
    rw [hB]
    simp only [Nat.mul_add,Nat.add_mul,Nat.one_mul]
    ac_rfl
  change 3*X*N+J+3*m+3=B*(J+3)
  rw [hBbase]
  rw [show 3*Q*(J+3)=3*(Q*(J+3)) by ac_rfl,hQJ]
  simp only [Nat.mul_add]
  ac_rfl

theorem towerX_power_two (m r : Nat) :
    towerX m r=2^((2*m+2)*r) := by
  dsimp [towerX,allOddB]
  exact (Nat.pow_mul 2 (2*m+2) r).symm

theorem towerX_positive (m r : Nat) : 1≤towerX m r := by
  dsimp [towerX]
  have hp : 0<allOddB m := by
    dsimp [allOddB]
    exact Nat.pow_pos (by decide)
  exact Nat.pow_pos hp

private theorem towerB_four (m : Nat) : allOddB m%4=0 := by
  dsimp [allOddB]
  rw [show 2*m+2=2+(2*m) by omega,Nat.pow_add]
  simp

theorem towerS_mod_four (m r : Nat) (hr : 1≤r) : towerS m r%4=1 := by
  cases r with
  | zero => omega
  | succ r =>
      have hB := towerB_four m
      change (allOddB m*towerS m r+1)%4=1
      rw [Nat.add_mod,Nat.mul_mod,hB]
      omega

theorem towerX_mod_four (m r : Nat) (hr : 1≤r) : towerX m r%4=0 := by
  have hQ := m8Geom4_mod_four (m+1) (by omega)
  have hS := towerS_mod_four m r hr
  have hX := towerX_geom m r
  have hQ4 : allOddQ m%4=1 := by simpa [allOddQ] using hQ
  rw [← hX, Nat.add_mod]
  have hprod : (3*allOddQ m*towerS m r)%4=3 := by
    have hfirst : (3*allOddQ m)%4=3 := by
      rw [Nat.mul_mod,hQ4]
    rw [Nat.mul_mod,hfirst,hS]
  rw [hprod]

theorem towerIndex_mod_four (m r t : Nat) (hr : 1≤r) :
    towerIndex m r t%4=(m+1)%4 := by
  have hQ := m8Geom4_mod_four (m+1) (by omega)
  have hQ4 : allOddQ m%4=1 := by simpa [allOddQ] using hQ
  have hQsub : (allOddQ m-1)%4=0 := by omega
  have hR : towerR m r%4=1 := by
    change (3*(allOddQ m-1)*towerS m r+1)%4=1
    rw [Nat.add_mod, Nat.mul_mod]
    have hp : (3*(allOddQ m-1))%4=0 := by
      rw [Nat.mul_mod,hQsub]
    rw [hp]
    simp
  have hX := towerX_mod_four m r hr
  have hS := towerS_mod_four m r hr
  have hSsub : (towerS m r-1)%4=0 := by omega
  have h1 : (towerR m r*(m+1))%4=(m+1)%4 := by
    rw [Nat.mul_mod,hR]
    simp only [Nat.one_mul, Nat.mod_mod]
  have h2 : (towerX m r*deepTail m t)%4=0 := by
    rw [Nat.mul_mod,hX]
    simp
  have h3 : (3*(towerS m r-1))%4=0 := by
    rw [Nat.mul_mod,hSsub]
  dsimp [towerIndex]
  omega

theorem towerN_at_least_two (m t : Nat) (hm : m%2=1) :
    2≤deepMass m t := by
  by_cases hm1 : m%4=1
  · have h := deepN_mod16_one m t hm1
    omega
  · have hm3 : m%4=3 := by omega
    have h := deepN_mod8_three m t hm3
    omega

theorem towerK_plus_two (m r t : Nat) (hm : m%2=1) :
    towerK m r t+2=3*towerX m r*deepMass m t := by
  have hn := towerN_at_least_two m t hm
  have hx := towerX_positive m r
  have hmul : 2≤towerX m r*deepMass m t := Nat.mul_le_mul hx hn
  have hmul3 : 6≤3*towerX m r*deepMass m t := by
    have h := Nat.mul_le_mul_left 3 hmul
    simpa [Nat.mul_assoc] using h
  dsimp [towerK]
  omega

theorem tower_stop (m r t : Nat) (hm : m%2=1) (hr : 1≤r) :
    towerK m r t+towerIndex m r t+3*m+5 =
      2^(2*m+2)*(towerIndex m r t+3) := by
  have hcalc := tower_stopping_algebra m r t hr
  have hk := towerK_plus_two m r t hm
  have hpow : allOddB m=2^(2*m+2) := rfl
  rw [hpow] at hcalc
  omega

theorem tower_every_odd_unreachable (m r t : Nat)
    (hm : m%2=1) (hr : 1≤r) :
    ¬ BB6.Agent15.CReach (2*towerIndex m r t+3) (towerK m r t) := by
  have hj4 := towerIndex_mod_four m r t hr
  have hj2 : towerIndex m r t%2=0 := by omega
  have hs : (towerIndex m r t+m)%4=3 := by omega
  have hstop := tower_stop m r t hm hr
  have hk := towerK_plus_two m r t hm
  have hE : ((2*m+2)*r)%4=0 := by
    have hbase : (2*m+2)%4=0 := by omega
    rw [Nat.mul_mod,hbase]
    simp
  by_cases hm1 : m%4=1
  · have hn16 := deepN_mod16_one m t hm1
    have hv8 : (deepMass m t/2)%8=2 := by omega
    have hnHalf : 2*(deepMass m t/2)=deepMass m t := by omega
    have hscale : towerK m r t+2=
        3*(deepMass m t/2)*2^((2*m+2)*r+1) := by
      calc
        towerK m r t+2=3*towerX m r*deepMass m t := hk
        _ = 3*2^((2*m+2)*r)*deepMass m t := by rw [towerX_power_two]
        _ = 3*(deepMass m t/2)*2^((2*m+2)*r+1) := by
          calc
            3*2^((2*m+2)*r)*deepMass m t =
                3*2^((2*m+2)*r)*(2*(deepMass m t/2)) :=
              congrArg (fun z : Nat => 3*2^((2*m+2)*r)*z) hnHalf.symm
            _ = 3*(deepMass m t/2)*2^((2*m+2)*r+1) := by
              rw [Nat.pow_succ]
              ac_rfl
    have hpar : 2*((2*m+2)*r+1)%4=(m+1)%4 := by omega
    exact deep_no_root_of_data (towerIndex m r t) m (towerK m r t)
      ((2*m+2)*r+1) (deepMass m t/2)
      hm hj2 hs hstop hscale hv8 hpar
  · have hm3 : m%4=3 := by omega
    have hn8 := deepN_mod8_three m t hm3
    have hscale : towerK m r t+2=
        3*deepMass m t*2^((2*m+2)*r) := by
      calc
        towerK m r t+2=3*towerX m r*deepMass m t := hk
        _ = 3*2^((2*m+2)*r)*deepMass m t := by rw [towerX_power_two]
        _ = 3*deepMass m t*2^((2*m+2)*r) := by ac_rfl
    have hpar : 2*((2*m+2)*r)%4=(m+1)%4 := by omega
    exact deep_no_root_of_data (towerIndex m r t) m (towerK m r t)
      ((2*m+2)*r) (deepMass m t) hm hj2 hs hstop hscale hn8 hpar

theorem tower_odd_depth (m r t : Nat) (hm : m%2=1) :
    BB6.Agent15.oddDepth (towerK m r t) =
      if m%4=1 then (2*m+2)*r+1 else (2*m+2)*r := by
  have hk := towerK_plus_two m r t hm
  by_cases hm1 : m%4=1
  · have hn16 := deepN_mod16_one m t hm1
    have hv8 : (deepMass m t/2)%8=2 := by omega
    have hnHalf : 2*(deepMass m t/2)=deepMass m t := by omega
    have hscale : towerK m r t+2=
        3*(deepMass m t/2)*2^((2*m+2)*r+1) := by
      calc
        towerK m r t+2=3*towerX m r*deepMass m t := hk
        _ = 3*2^((2*m+2)*r)*deepMass m t := by rw [towerX_power_two]
        _ = 3*(deepMass m t/2)*2^((2*m+2)*r+1) := by
          calc
            3*2^((2*m+2)*r)*deepMass m t =
                3*2^((2*m+2)*r)*(2*(deepMass m t/2)) :=
              congrArg (fun z : Nat => 3*2^((2*m+2)*r)*z) hnHalf.symm
            _ = 3*(deepMass m t/2)*2^((2*m+2)*r+1) := by
              rw [Nat.pow_succ]
              ac_rfl
    have hv4 : (deepMass m t/2)%4=2 := by omega
    have heq : towerK m r t =
        3*(deepMass m t/2)*2^((2*m+2)*r+1)-2 := by omega
    rw [heq, m8OddDepth_scaled (deepMass m t/2) ((2*m+2)*r+1) hv4]
    simp [hm1]
  · have hm3 : m%4=3 := by omega
    have hn8 := deepN_mod8_three m t hm3
    have hscale : towerK m r t+2=
        3*deepMass m t*2^((2*m+2)*r) := by
      calc
        towerK m r t+2=3*towerX m r*deepMass m t := hk
        _ = 3*2^((2*m+2)*r)*deepMass m t := by rw [towerX_power_two]
        _ = 3*deepMass m t*2^((2*m+2)*r) := by ac_rfl
    have hv4 : deepMass m t%4=2 := by omega
    have heq : towerK m r t=3*deepMass m t*2^((2*m+2)*r)-2 := by omega
    rw [heq,m8OddDepth_scaled (deepMass m t) ((2*m+2)*r) hv4]
    simp [hm1]

#print axioms tower_every_odd_unreachable
#print axioms tower_odd_depth
#print axioms tower_stopping_algebra
end BB6.Agent15Research

