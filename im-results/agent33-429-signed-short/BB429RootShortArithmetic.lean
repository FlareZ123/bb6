import Lean

namespace BB429RootShortArithmetic
set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

/-- The exact source-compatible inverse equations for positive outputs:
  F for odd outputs, S for odd outputs with lower congruence two,
  E for even outputs with lower congruence two. -/
def Parent (a b x y : Nat) : Prop :=
  (a % 2 = 1 ∧ a = 2*x+3 ∧ y = b+a) ∨
  (a % 2 = 1 ∧ b % 4 = 2 ∧ 4*x+26 = 4*a+b ∧ 2*y = b+4) ∨
  (a % 2 = 0 ∧ b % 4 = 2 ∧ 4*x+14 = 4*a+b ∧ 2*y = b)

/-- Three *original-source necessary* modular gates. Every genuinely
    blank-reachable state obeys these, by RootEven8, RootMod16 and Mod8. -/
def Gate (u w : Nat) : Prop :=
 (0<u → u%2=0 → w%8=2) ∧
 (u%8=7 → w%8≠7) ∧
 (u%8=1 → w%4≠3)

/-- No length-4 authentic-shape source inverse prefix can have all
    predecessors satisfying the recorded all-time modular gate. -/
theorem branch13_q2_no_four
    (t u1 w1 u2 w2 u3 w3 u4 w4 : Nat)
    (h1 : Parent (128*t+77) (256*t+151) u1 w1)
    (h2 : Parent u1 w1 u2 w2)
    (h3 : Parent u2 w2 u3 w3)
    (h4 : Parent u3 w3 u4 w4)
    (g1 : Gate u1 w1)
    (g2 : Gate u2 w2)
    (g3 : Gate u3 w3)
    (g4 : Gate u4 w4) : False := by
  unfold Parent Gate at *
  omega

/-- No length-4 authentic-shape source inverse prefix can have all
    predecessors satisfying the recorded all-time modular gate. -/
theorem branch13_q3_no_four
    (t u1 w1 u2 w2 u3 w3 u4 w4 : Nat)
    (h1 : Parent (128*t+109) (256*t+215) u1 w1)
    (h2 : Parent u1 w1 u2 w2)
    (h3 : Parent u2 w2 u3 w3)
    (h4 : Parent u3 w3 u4 w4)
    (g1 : Gate u1 w1)
    (g2 : Gate u2 w2)
    (g3 : Gate u3 w3)
    (g4 : Gate u4 w4) : False := by
  unfold Parent Gate at *
  omega

/-- No length-5 authentic-shape source inverse prefix can have all
    predecessors satisfying the recorded all-time modular gate. -/
theorem branch15_q1_no_five
    (t u1 w1 u2 w2 u3 w3 u4 w4 u5 w5 : Nat)
    (h1 : Parent (128*t+47) (256*t+91) u1 w1)
    (h2 : Parent u1 w1 u2 w2)
    (h3 : Parent u2 w2 u3 w3)
    (h4 : Parent u3 w3 u4 w4)
    (h5 : Parent u4 w4 u5 w5)
    (g1 : Gate u1 w1)
    (g2 : Gate u2 w2)
    (g3 : Gate u3 w3)
    (g4 : Gate u4 w4)
    (g5 : Gate u5 w5) : False := by
  unfold Parent Gate at *
  omega

#print axioms branch13_q2_no_four
#print axioms branch13_q3_no_four
#print axioms branch15_q1_no_five
end BB429RootShortArithmetic
