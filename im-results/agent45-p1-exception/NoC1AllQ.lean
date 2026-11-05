import NoC1Source

set_option maxRecDepth 8192
namespace BB6.Agent45Exception
open BB6.P1Reduction

/-- Exponential scale dominates the entire 15q inverse cost budget
once q ≥ 12. -/
private theorem exponential_margin_from_12 (r : Nat) :
    2*(31*(r+12)+9) < 2^(r+10) := by
  induction r with
  | zero => decide
  | succ r ih =>
      have hpow : 2^((r+1)+10)=2*(2^(r+10)) := by
        have he : (r+1)+10=(r+10)+1 := by omega
        rw [he, Nat.pow_succ]
        omega
      rw [hpow]
      have hp : 0 < 2^(r+10) := Nat.two_pow_pos _
      omega

theorem uniform_margin_above_12 (q L m : Nat)
    (hq : 12≤q) (hL : L≤16*q+9) (hm : m≤15*q) :
    2*(L+m) < 2^(16*q-m-2) := by
  let r := q-12
  have hr : q=r+12 := by dsimp [r]; omega
  have hb : 2*(31*q+9)<2^(q-2) := by
    have ht := exponential_margin_from_12 r
    have he : (r+12)-2=r+10 := by omega
    rw [hr, he]
    exact ht
  have he : q-2≤16*q-m-2 := by omega
  have hpow := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) he
  omega

/-- Every safely encoded original P1 n=16q+2 feeder odd cone of
cost m≤15q, for q≥12, excludes all exceptional G(k,1) parents. -/
theorem no_special_G_one_above_12
    (q L m b d w z alpha k : Nat)
    (hq : 12≤q) (hL : L≤16*q+9) (hm : m≤15*q)
    (hw : 4≤w) (hz : 0<z)
    (hbeven : b%2=0) (hbpos : 0<b)
    (hmass : b+d+2*m+2*L+3=56*2^(16*q))
    (hoff : L+m=w+z)
    (hcoord : b+4*w=alpha*2^(16*q-m))
    (hG : G k 1=(b,d)) : False := by
  have hmargin := uniform_margin_above_12 q L m hq hL hm
  have hsafe : m+4≤16*q := by omega
  exact encoded_no_special_G_one (16*q) L m b d w z alpha k
    hsafe hw hz hbeven hbpos hmass hoff hcoord hmargin hG

#print axioms uniform_margin_above_12
#print axioms no_special_G_one_above_12
end BB6.Agent45Exception
