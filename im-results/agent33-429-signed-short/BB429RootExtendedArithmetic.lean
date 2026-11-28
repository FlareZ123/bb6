import BB429RootShortArithmetic

namespace BB429RootExtendedArithmetic
open BB429RootShortArithmetic
set_option maxHeartbeats 150000000
set_option maxRecDepth 100000

/-! Source-independent symbolic all-congruence finite inverse certificates.
    Each family is quantified over ALL t>=1, every choice of inverse edge,
    and every predecessor satisfying three original blank-root gates. -/

theorem branch13_q0mod8_no_eight
    (t u1 w1 u2 w2 u3 w3 u4 w4 u5 w5 u6 w6 u7 w7 u8 w8 : Nat)
    (ht : 1 ≤ t)
    (h1 : Parent (256*t+13) (512*t+23) u1 w1)
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
    (g8 : Gate u8 w8) : False := by
  unfold Parent Gate at *
  omega

theorem branch13_q1mod8_no_eight
    (t u1 w1 u2 w2 u3 w3 u4 w4 u5 w5 u6 w6 u7 w7 u8 w8 : Nat)
    (ht : 1 ≤ t)
    (h1 : Parent (256*t+45) (512*t+87) u1 w1)
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
    (g8 : Gate u8 w8) : False := by
  unfold Parent Gate at *
  omega

theorem branch13_q5mod16_no_nine
    (t u1 w1 u2 w2 u3 w3 u4 w4 u5 w5 u6 w6 u7 w7 u8 w8 u9 w9 : Nat)
    (ht : 1 ≤ t)
    (h1 : Parent (512*t+173) (1024*t+343) u1 w1)
    (h2 : Parent u1 w1 u2 w2)
    (h3 : Parent u2 w2 u3 w3)
    (h4 : Parent u3 w3 u4 w4)
    (h5 : Parent u4 w4 u5 w5)
    (h6 : Parent u5 w5 u6 w6)
    (h7 : Parent u6 w6 u7 w7)
    (h8 : Parent u7 w7 u8 w8)
    (h9 : Parent u8 w8 u9 w9)
    (g1 : Gate u1 w1)
    (g2 : Gate u2 w2)
    (g3 : Gate u3 w3)
    (g4 : Gate u4 w4)
    (g5 : Gate u5 w5)
    (g6 : Gate u6 w6)
    (g7 : Gate u7 w7)
    (g8 : Gate u8 w8)
    (g9 : Gate u9 w9) : False := by
  unfold Parent Gate at *
  omega

theorem branch15_q2mod8_no_eight
    (t u1 w1 u2 w2 u3 w3 u4 w4 u5 w5 u6 w6 u7 w7 u8 w8 : Nat)
    (ht : 1 ≤ t)
    (h1 : Parent (256*t+79) (512*t+155) u1 w1)
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
    (g8 : Gate u8 w8) : False := by
  unfold Parent Gate at *
  omega

#print axioms branch13_q0mod8_no_eight
#print axioms branch13_q1mod8_no_eight
#print axioms branch13_q5mod16_no_nine
#print axioms branch15_q2mod8_no_eight
end BB429RootExtendedArithmetic
