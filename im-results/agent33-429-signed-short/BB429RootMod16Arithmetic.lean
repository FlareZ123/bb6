import BB429RootShortArithmetic

namespace BB429RootMod16Arithmetic
open BB429RootShortArithmetic
set_option maxHeartbeats 300000000
set_option maxRecDepth 100000

/-! Three-stage inverse congruence sieve for the entire #429
    13-last-reset line, with zero finite scans or signed truncation. -/

/-- A length-4 inverse chain in the authentic necessary modular gate
    forces the following quotient-state congruence. -/
theorem after_four
    (q u1 w1 u2 w2 u3 w3 u4 w4 : Nat)
    (h1 : Parent (32*q+13) (64*q+23) u1 w1)
    (h2 : Parent u1 w1 u2 w2)
    (h3 : Parent u2 w2 u3 w3)
    (h4 : Parent u3 w3 u4 w4)
    (g1 : Gate u1 w1)
    (g2 : Gate u2 w2)
    (g3 : Gate u3 w3)
    (g4 : Gate u4 w4) :
    q%4=0 ∨ q%4=1 := by
  unfold Parent Gate at *
  omega

/-- A length-7 inverse chain in the authentic necessary modular gate
    forces the following quotient-state congruence. -/
theorem after_seven
    (q u1 w1 u2 w2 u3 w3 u4 w4 u5 w5 u6 w6 u7 w7 : Nat)
    (h1 : Parent (32*q+13) (64*q+23) u1 w1)
    (h2 : Parent u1 w1 u2 w2)
    (h3 : Parent u2 w2 u3 w3)
    (h4 : Parent u3 w3 u4 w4)
    (h5 : Parent u4 w4 u5 w5)
    (h6 : Parent u5 w5 u6 w6)
    (h7 : Parent u6 w6 u7 w7)
    (g1 : Gate u1 w1)
    (g2 : Gate u2 w2)
    (g3 : Gate u3 w3)
    (g4 : Gate u4 w4)
    (g5 : Gate u5 w5)
    (g6 : Gate u6 w6)
    (g7 : Gate u7 w7) :
    q%8=4 ∨ q%8=5 := by
  have hmod := after_four q u1 w1 u2 w2 u3 w3 u4 w4 h1 h2 h3 h4 g1 g2 g3 g4
  unfold Parent Gate at *
  omega

/-- A length-8 inverse chain in the authentic necessary modular gate
    forces the following quotient-state congruence. -/
theorem after_eight
    (q u1 w1 u2 w2 u3 w3 u4 w4 u5 w5 u6 w6 u7 w7 u8 w8 : Nat)
    (h1 : Parent (32*q+13) (64*q+23) u1 w1)
    (h2 : Parent u1 w1 u2 w2)
    (h3 : Parent u2 w2 u3 w3)
    (h4 : Parent u3 w3 u4 w4)
    (h5 : Parent u4 w4 u5 w5)
    (h6 : Parent u5 w5 u6 w6)
    (h7 : Parent u6 w6 u7 w7)
    (h8 : Parent u7 w7 u8 w8)
    (g1 : Gate u1 w1)
    (g2 : Gate u2 w2)
    (g3 : Gate u3 w3)
    (g4 : Gate u4 w4)
    (g5 : Gate u5 w5)
    (g6 : Gate u6 w6)
    (g7 : Gate u7 w7)
    (g8 : Gate u8 w8) :
    q%16=4 ∨ q%16=12 ∨ q%16=13 := by
  have hmod := after_seven q u1 w1 u2 w2 u3 w3 u4 w4 u5 w5 u6 w6 u7 w7 h1 h2 h3 h4 h5 h6 h7 g1 g2 g3 g4 g5 g6 g7
  unfold Parent Gate at *
  omega


#print axioms after_four
#print axioms after_seven
#print axioms after_eight
end BB429RootMod16Arithmetic
