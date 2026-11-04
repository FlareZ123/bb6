import SpaceNeedleOddBlocksSource
import NeedleTwoStepOdd
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace BB6.Agent48.NeedleTwoStepOddBridge
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle
open BB6.Agent48.NeedleTwoStepOdd

private theorem destination_identity (q v : Nat) :
  oddTower q v+v+3*(q+1)+2=destinationPlusTwo q v := by
  have hf := oddTower_factor q v
  calc
    oddTower q v+v+3*(q+1)+2
        = 2^v*(2*q+3)+v+3*(q+1) := by omega
    _ = destinationPlusTwo q v := by
      dsimp [destinationPlusTwo,den,bias]
      rw [Nat.pow_succ']
      simp only [Nat.mul_add, Nat.add_mul]
      have hmul : 2^v*(2*q) = (2*2^v)*q := by ac_rfl
      omega

private theorem original_odd_tower_step (q v : Nat) :
  highLevelNext (.N (oddTower q v)) =
    some (.N (oddTower q v+v+3*(q+1))) := by
  simpa [highLevelNext] using scan_oddTower q v 0

private theorem two_pow_ge_two (K : Nat) (hK : 0<K) : 2 ≤ (2:Nat)^K := by
  have h := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (show 1≤K by omega)
  simpa using h

/-- Exact original high-level semantics of the two-step odd-terminal family.
The entry is any oddTower q v, the intermediate counter is odd, and the
second successful transition reaches a terminal input of exponent K. -/
theorem original_two_step_odd_iff (q v K : Nat) (hK : 0<K) :
  (∃ e, highLevelNext (.N (oddTower q v)) = some (.N e) ∧
      e%2=1 ∧ highLevelNext (.N e) = some (.N (2^K-2))) ↔
    2^(K+1)=modulus v*q+offset v := by
  rw [←two_step_odd_expanded]
  constructor
  · rintro ⟨e,hfirst,heodd,hlast⟩
    have heq : e=oddTower q v+v+3*(q+1) := by
      rw [original_odd_tower_step] at hfirst
      simpa only [Option.some.injEq, HighLevelState.N.injEq] using hfirst.symm
    let a := e/2+1
    have ha : 0<a := by dsimp [a]; omega
    have hshape : e=2*a-1 := by dsimp [a]; omega
    have hsecond := odd_step a ha
    rw [←hshape] at hsecond
    rw [hsecond] at hlast
    have hterm : 5*a+1=2^K := by
      have hbig := two_pow_ge_two K hK
      simp only [Option.some.injEq, HighLevelState.N.injEq] at hlast
      omega
    have hdest : destinationPlusTwo q v=2*a+1 := by
      rw [←destination_identity]
      omega
    exact ⟨a,hdest,hterm⟩
  · rintro ⟨a,hdest,hpower⟩
    have ha : 0<a := by
      have hbig : 6 ≤ destinationPlusTwo q v := by
        dsimp [destinationPlusTwo,den,bias]
        have hpow : 0<(2:Nat)^v := Nat.pow_pos (by decide)
        omega
      omega
    let e := 2*a-1
    have heq : oddTower q v+v+3*(q+1)=e := by
      rw [←destination_identity] at hdest
      dsimp [e]
      omega
    have hfirst : highLevelNext (.N (oddTower q v))=some (.N e) := by
      rw [original_odd_tower_step,heq]
    have hodd : e%2=1 := by dsimp [e]; omega
    have hsecond : highLevelNext (.N e)=some (.N (2^K-2)) := by
      change highLevelNext (.N (2*a-1)) = some (.N (2^K-2))
      rw [odd_step a ha]
      have hbig := two_pow_ge_two K hK
      have hterm : 5*a-1=2^K-2 := by omega
      rw [hterm]
    exact ⟨e,hfirst,hodd,hsecond⟩

#print axioms original_two_step_odd_iff
end BB6.Agent48.NeedleTwoStepOddBridge
