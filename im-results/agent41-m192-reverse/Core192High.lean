import Quotient192
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace Agent41M192

def high (a k c : Nat) : Prop :=
  let d := (a + 192 - c%192)%192
  let t := (a+k)%192
  let u := (t+48*(d/96))%96
  (d%96=0 ∧ u=63) ∨
  (d%96=7 ∧ u=66) ∨
  (d%96=24 ∧ u=75) ∨
  (d%96=31 ∧ u=78) ∨
  (d%96=33 ∧ (u=81 ∨ u=83)) ∨
  (d%96=48 ∧ u=87) ∨
  (d%96=55 ∧ u=90) ∨
  (d%96=72 ∧ u=3) ∨
  (d%96=79 ∧ u=6) ∨
  (d%96=81 ∧ u=9) ∨
  (d=6 ∧ t=73) ∨
  (d=125 ∧ t%96=35)

theorem high_a_pos (a k c:Nat) (ha:0<a) (hc:8<c) :
  high (a-1) (k+1) (c-1) → high a k c := by
  intro h
  have hd : (a-1+192-(c-1)%192)%192=(a+192-c%192)%192 := by omega
  have ht : ((a-1)+(k+1))%192=(a+k)%192 := by omega
  simp only [high] at h ⊢
  rw [hd,ht] at h
  exact h

private theorem high_no_sum_zero_mod4 (a k c:Nat) (h : (a+k)%4=0) : ¬high a k c := by
  simp only [high]
  intro hhigh
  have hm : ((a+k)%192)%4=0 := by omega
  rcases hhigh with h|h|h|h|h|h|h|h|h|h|h|h <;> omega

#print axioms high_a_pos
#print axioms high_no_sum_zero_mod4
end Agent41M192
