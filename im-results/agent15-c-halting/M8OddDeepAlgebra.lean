import M8AllOddExplicit
import Lean.Elab.Tactic.Omega
namespace BB6.Agent15Research

/-- A geometric quotient stopping equation with arbitrary tail parameter. -/
theorem deep_algebra (B Q m T : Nat)
    (hB : B=3*Q+1) (hQ : 1≤Q) (_hbound : 3≤B) :
    let J := (B-3)*(m+1)+B*T
    let N := (Q-1)*m+Q*(T+1)
    3*B*N+J+3*m+3=B*(J+3) := by
  let J := (B-3)*(m+1)+B*T
  let N := (Q-1)*m+Q*(T+1)
  have hBsub : B-3+3=B := by omega
  have hQsub : Q-1+1=Q := by omega
  have hJ : J+3+3*m=B*(m+T+1) := by
    have hmul : (B-3)*(m+1)+3*(m+1)=B*(m+1) := by
      calc
        (B-3)*(m+1)+3*(m+1)=(B-3+3)*(m+1) := (Nat.add_mul (B-3) 3 (m+1)).symm
        _=B*(m+1) := by rw [hBsub]
    calc
      J+3+3*m=(B-3)*(m+1)+3*(m+1)+B*T := by dsimp [J]; omega
      _=B*(m+1)+B*T := by rw [hmul]
      _=B*(m+T+1) := by
        rw [show m+T+1=(m+1)+T by omega]
        simp only [Nat.mul_add,Nat.mul_one]
  have hN : N+m=Q*(m+T+1) := by
    change (Q-1)*m+Q*(T+1)+m=Q*(m+T+1)
    calc
      (Q-1)*m+Q*(T+1)+m=(Q-1+1)*m+Q*(T+1) := by
        simp only [Nat.add_mul,Nat.one_mul]
        ac_rfl
      _=Q*(m+T+1) := by
        rw [hQsub,show m+T+1=m+(T+1) by omega]
        simp only [Nat.mul_add]
  have hQJ : Q*(J+3)=B*N+m := by
    have hp : Q*(J+3)+3*Q*m=B*(N+m) := by
      calc
        Q*(J+3)+3*Q*m=Q*(J+3+3*m) := by
          simp only [Nat.mul_add,Nat.mul_assoc]
          ac_rfl
        _=Q*(B*(m+T+1)) := by rw [hJ]
        _=B*(Q*(m+T+1)) := by ac_rfl
        _=B*(N+m) := by rw [hN]
    have hh : B*(N+m)=B*N+3*Q*m+m := by
      rw [hB]
      simp only [Nat.mul_add,Nat.add_mul,Nat.one_mul]
      ac_rfl
    rw [hh] at hp
    omega
  have hBbase : B*(J+3)=3*Q*(J+3)+(J+3) := by
    rw [hB]
    simp only [Nat.mul_add,Nat.add_mul,Nat.one_mul]
    ac_rfl
  change 3*B*N+J+3*m+3=B*(J+3)
  rw [hBbase]
  rw [show 3*Q*(J+3)=3*(Q*(J+3)) by ac_rfl,hQJ]
  simp only [Nat.mul_add]
  ac_rfl
end BB6.Agent15Research
