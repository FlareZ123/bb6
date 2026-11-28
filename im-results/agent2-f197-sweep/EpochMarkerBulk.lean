import EpochEntrance
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace F197.Agent2EpochMarker

theorem hpow_comm (n : Nat) (r : Tape) : hpow n (h r) = h (hpow n r) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [hpow]; rw [ih]

theorem hsingle_even (n : Nat) (r : Tape) : hsingle (2*n) r = hpow n r := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1) = 2*n+2 by omega]
    change h (h (hsingle (2*n) r)) = h (h (hpow n r))
    rw [ih]

theorem middle0 (n : Nat) (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run ((scancost (2*n+1)+112)+cost n)
      (b (kpow (2*n+1) (source l)) r) = some (b (g (blockpow n (t l))) (v r)) := by
  have h1 := scan_many (2*n+1) (source l) r (by rfl) hr
  have hs : hsingle (2*n+1) r = h (hpow n r) := by
    change h (hsingle (2*n) r) = _
    rw [hsingle_even]
  rw [hs] at h1
  have h2 := entry l (hpow n r) hl (hpow_first n r hr)
  have h3 := cycle_many n (t l) r (by rfl) hr
  exact @compose (scancost (2*n+1)+112) (cost n) _ _ _
    (@compose (scancost (2*n+1)) 112 _ _ _ h1 h2) h3

theorem middle1 (n : Nat) (l r : Tape) (hl : l 0 = true) (hr : r 0 = true) :
    run (((scancost (2*n+2)+112)+cost n)+176)
      (b (kpow (2*n+2) (source l)) r) = some (b (g2 (blockpow n (t l))) (v2 r)) := by
  have h1 := scan_many (2*n+2) (source l) r (by rfl) hr
  have hs : hsingle (2*n+2) r = h (hpow n (h r)) := by
    change h (h (hsingle (2*n) r)) = _
    rw [hsingle_even, hpow_comm]
  rw [hs] at h1
  have h2 := entry l (hpow n (h r)) hl (hpow_first n (h r) (by rfl))
  have h3 := cycle_many n (t l) (h r) (by rfl) (by rfl)
  have h4 := half (blockpow n (t l)) r (by cases n <;> rfl) hr
  exact @compose ((scancost (2*n+2)+112)+cost n) 176 _ _ _
    (@compose (scancost (2*n+2)+112) (cost n) _ _ _
      (@compose (scancost (2*n+2)) 112 _ _ _ h1 h2) h3) h4

/-- Even descent endpoint, odd remaining K count. -/
theorem bulk00 (n : Nat) (l : Tape) (hl : l 0 = true) :
    run ((1863+((scancost (2*n+1)+112)+cost n))+806)
      (b (ent0 (kpow (2*n+1) (source l))) (pre [true] blank)) =
    some (b (out0g (blockpow n (t l))) (pre [true] blank)) := by
  have h1 := enter0 (kpow (2*n+1) (source l)) (kpow_first _ _ (by rfl))
  have h2 := middle0 n l r0 hl (by rfl)
  have h3 := exit0g (blockpow n (t l)) (by cases n <;> rfl)
  exact @compose (1863+((scancost (2*n+1)+112)+cost n)) 806 _ _ _
    (@compose 1863 ((scancost (2*n+1)+112)+cost n) _ _ _ h1 h2) h3

/-- Even descent endpoint, even remaining K count. -/
theorem bulk01 (n : Nat) (l : Tape) (hl : l 0 = true) :
    run ((1863+(((scancost (2*n+2)+112)+cost n)+176))+698)
      (b (ent0 (kpow (2*n+2) (source l))) (pre [true] blank)) =
    some (b (out0g2 (blockpow n (t l))) (pre [true] blank)) := by
  have h1 := enter0 (kpow (2*n+2) (source l)) (kpow_first _ _ (by rfl))
  have h2 := middle1 n l r0 hl (by rfl)
  have h3 := exit0g2 (blockpow n (t l)) (by cases n <;> rfl)
  exact @compose (1863+(((scancost (2*n+2)+112)+cost n)+176)) 698 _ _ _
    (@compose 1863 (((scancost (2*n+2)+112)+cost n)+176) _ _ _ h1 h2) h3

/-- Odd descent endpoint, odd K count. -/
theorem bulk10 (n : Nat) (l : Tape) (hl : l 0 = true) :
    run ((887+((scancost (2*n+1)+112)+cost n))+407)
      (b (ent1 (kpow (2*n+1) (source l))) (pre [true] blank)) =
    some (b (out1g (blockpow n (t l))) (pre [true] blank)) := by
  have h1 := enter1 (kpow (2*n+1) (source l)) (kpow_first _ _ (by rfl))
  have h2 := middle0 n l r1 hl (by rfl)
  have h3 := exit1g (blockpow n (t l)) (by cases n <;> rfl)
  exact @compose (887+((scancost (2*n+1)+112)+cost n)) 407 _ _ _
    (@compose 887 ((scancost (2*n+1)+112)+cost n) _ _ _ h1 h2) h3

/-- Odd descent endpoint, even K count. -/
theorem bulk11 (n : Nat) (l : Tape) (hl : l 0 = true) :
    run ((887+(((scancost (2*n+2)+112)+cost n)+176))+599)
      (b (ent1 (kpow (2*n+2) (source l))) (pre [true] blank)) =
    some (b (out1g2 (blockpow n (t l))) (pre [true] blank)) := by
  have h1 := enter1 (kpow (2*n+2) (source l)) (kpow_first _ _ (by rfl))
  have h2 := middle1 n l r1 hl (by rfl)
  have h3 := exit1g2 (blockpow n (t l)) (by cases n <;> rfl)
  exact @compose (887+(((scancost (2*n+2)+112)+cost n)+176)) 599 _ _ _
    (@compose 887 (((scancost (2*n+2)+112)+cost n)+176) _ _ _ h1 h2) h3

theorem costs (n : Nat) :
    ((1863+((scancost (2*n+1)+112)+cost n))+806 = 2863+436*n) ∧
    ((1863+(((scancost (2*n+2)+112)+cost n)+176))+698 = 3013+436*n) ∧
    ((887+((scancost (2*n+1)+112)+cost n))+407 = 1488+436*n) ∧
    ((887+(((scancost (2*n+2)+112)+cost n)+176))+599 = 1938+436*n) := by
  simp only [scancost_eq,cost_eq]; omega

#print axioms bulk00
#print axioms bulk01
#print axioms bulk10
#print axioms bulk11
#print axioms costs
end F197.Agent2EpochMarker
