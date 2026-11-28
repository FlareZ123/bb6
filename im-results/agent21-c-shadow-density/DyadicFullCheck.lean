import DyadicBad
import DyadicValuation

namespace BB6.Agent21Duality
open BB6.Agent42ModularCone
open BB6.Agent21Dyadic

/-- A 2^b-divisible signed Q never triggers Bad when b>=2. -/
theorem divisible_not_bad (b : Nat) (s : Pair) (hb : 2≤b)
    (hd : I b∣q s) : ¬Bad s := by
  intro hbad
  have hbad' := bad_implies_not_open b s hb hbad
  have hopen : OpenAt (signedS s.x s.y) (signedZ s.x s.y) b := by
    apply signed_open_if_divisible s.x s.y b (by omega)
    have he : q s=s.x+s.y+(s.x+s.y)%2 := rfl
    have hpow : (P b:Int)=I b := by simp [P,I,BB6.Agent42ModularCone.P]
    rw [he,←hpow] at hd
    exact hd
  exact hbad' hopen

/-- When 2^b divides the adjusted sum, the modular cone checker
    necessarily returns false for every strictly positive fuel. -/
theorem check_full_division (b f : Nat) (s : Pair)
    (hb : 2≤b) (hd : I b∣q s) :
    check (f+1) b s=false := by
  have hbad : ¬Bad s := divisible_not_bad b s hb hd
  have hval : ¬ValValid b s (valuation b (q s)) := by
    intro h
    exact (valvalid_iff_not_divisible b s).mp h hd
  simp [check,hb,hbad,hval]

#print axioms check_full_division
end BB6.Agent21Duality
