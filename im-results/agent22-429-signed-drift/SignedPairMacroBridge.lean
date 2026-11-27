import PeriodicMacroTransfer

namespace SignedPairMacroBridge

inductive FRun : Nat → Nat → Nat → Nat → Nat → Prop where
  | zero (u d : Nat) : FRun 0 u d u d
  | step {m u d um dm : Nat} (hu : u%2=0)
      (tail : FRun m (u/2) (d+3*u+3) um dm) :
      FRun (m+1) u d um dm

theorem fRun_rank {m u d um dm : Nat} (h : FRun m u d um dm) :
    dm + 6*um = d+6*u+3*m := by
  induction h with
  | zero u d => simp
  | @step m u d um dm hu tail ih =>
    have hdiv : u=2*(u/2) := by omega
    omega

theorem fRun_power {m u d um dm : Nat} (h : FRun m u d um dm) :
    u = 2^m * um := by
  induction h with
  | zero u d => simp
  | @step m u d um dm hu tail ih =>
    have hdiv : u=2*(u/2) := by omega
    calc
      u = 2*(u/2) := hdiv
      _ = 2 * (2^m * um) := by rw [ih]
      _ = 2^(m+1) * um := by simp [Nat.pow_succ,Nat.mul_comm,Nat.mul_left_comm]

theorem fRun_parity {m u d um dm : Nat} (h : FRun m u d um dm) :
    dm%2=(d+m)%2 := by
  induction h with
  | zero u d => simp
  | @step m u d um dm hu tail ih =>
    omega

inductive PairRun : Bool → Nat → Nat → Nat → Nat → Nat → Prop where
  | e {j u D v d' : Nat} (hj : 0<j) (hu : u%2=1) (hD : D%8=0)
      (tail : FRun (2*(j-1)) (u+(D+8)/8) (D/4+4) v d') :
      PairRun true j u D v d'
  | s {j u D v d' : Nat} (hj : 0<j) (hu : u%2=0) (hD : D%8=4)
      (tail : FRun (2*(j-1)) (u+(D+20)/8) (D/4-1) v d') :
      PairRun false j u D v d'

private theorem exp (j : Nat) (hj : 0<j) :
    4^j = 4*(2^(2*(j-1))) := by
  have hpow4 : 4^(j-1) = 2^(2*(j-1)) := by
    have hh := Nat.pow_mul 2 2 (j-1)
    change 2^(2*(j-1)) = 4^(j-1) at hh
    exact hh.symm
  calc
    4^j = 4^((j-1)+1) := by congr 1; omega
    _ = 4^(j-1)*4 := by rw [Nat.pow_succ]
    _ = 4*(2^(2*(j-1))) := by rw [hpow4]; omega

/-- Exact signed F/EF/SF coordinates imply the affine model,
    assuming integer half-ranks at input and output. -/
theorem pairRun_model {typ : Bool} {j u D v d' r s : Nat}
    (h : PairRun typ j u D v d') (hr : 6*u+D=2*r)
    (hs : 6*v+d'=2*s) :
    PeriodicMacro.Step ⟨j,typ⟩ u r v s := by
  cases h with
  | @e j u D v d' hj hu hD fr =>
    have hpow := fRun_power fr
    have hrank := fRun_rank fr
    have he := exp j hj
    have hd : D=8*(D/8) := by omega
    have hsum : (D+8)/8 = D/8+1 := by omega
    have hq : D/4 = 2*(D/8) := by omega
    change 4^j*v=u+r+4 ∧ s=r+3*j+2
    have h4 : 4^j*v = 4*(u+(D+8)/8) := by
      calc
        4^j*v = 4*(2^(2*(j-1))*v) := by rw [he]; simp [Nat.mul_assoc]
        _ = 4*(u+(D+8)/8) := by rw [hpow]
    constructor
    · rw [hsum] at h4
      omega
    · rw [hsum,hq] at hrank
      omega
  | @s j u D v d' hj hu hD fr =>
    have hpow := fRun_power fr
    have hrank := fRun_rank fr
    have he := exp j hj
    have hd : D=8*(D/8)+4 := by omega
    have hsum : (D+20)/8 = D/8+3 := by omega
    have hq : D/4-1 = 2*(D/8) := by omega
    change 4^j*v=u+r+10 ∧ s=r+3*j+4
    have h4 : 4^j*v = 4*(u+(D+20)/8) := by
      calc
        4^j*v = 4*(2^(2*(j-1))*v) := by rw [he]; simp [Nat.mul_assoc]
        _ = 4*(u+(D+20)/8) := by rw [hpow]
    constructor
    · rw [hsum] at h4
      omega
    · rw [hsum,hq] at hrank
      omega

theorem pairRun_output_even {typ : Bool} {j u D v d' : Nat}
    (h : PairRun typ j u D v d') : d'%2=0 := by
  cases h with
  | @e j u D v d' hj hu hD fr =>
    have hp := fRun_parity fr
    have hde : (D/4+4)%2=0 := by omega
    omega
  | @s j u D v d' hj hu hD fr =>
    have hp := fRun_parity fr
    have hde : (D/4-1)%2=0 := by omega
    omega

/-- No separately supplied output half-rank is required. -/
theorem pairRun_model_exists {typ : Bool} {j u D v d' r : Nat}
    (h : PairRun typ j u D v d') (hr : 6*u+D=2*r) :
    ∃ s : Nat, 6*v+d'=2*s ∧
      PeriodicMacro.Step ⟨j,typ⟩ u r v s := by
  have hde := pairRun_output_even h
  let s : Nat := (6*v+d')/2
  have hs : 6*v+d'=2*s := by dsimp [s]; omega
  exact ⟨s,hs,pairRun_model h hr hs⟩

#print axioms pairRun_model_exists
#print axioms pairRun_output_even
#print axioms fRun_parity
#print axioms pairRun_model
end SignedPairMacroBridge
