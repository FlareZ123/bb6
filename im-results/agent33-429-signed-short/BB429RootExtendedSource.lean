import BB429RootShortSource
import BB429RootExtendedArithmetic

namespace BB429RootExtendedSource
open BB429NewResidue
open BB429RootShortArithmetic
open BB429RootShortSource

set_option maxHeartbeats 150000000
set_option maxRecDepth 100000

/-! Authentic blank-origin inverse witnesses transported through
    all-time BB429RootEven8 / Mod8 / Mod16 constraints. -/

theorem branch13_q0mod8_unreachable (t : Nat) (ht : 1 ≤ t) :
    ¬ Reach (256*t+13) (512*t+23) := by
  intro h0
  obtain ⟨u1,w1,hr1,hp1⟩ :=
    parent_of_reach (256*t+13) (512*t+23) (by omega) h0
  obtain ⟨u2,w2,hr2,hp2⟩ :=
    parent_of_reach u1 w1 (by
      have h1' := hp1
      have g1' := gate_of_reach u1 w1 hr1
      unfold Parent at h1'
      unfold Gate at g1'
      omega) hr1
  obtain ⟨u3,w3,hr3,hp3⟩ :=
    parent_of_reach u2 w2 (by
      have h1' := hp1
      have g1' := gate_of_reach u1 w1 hr1
      have h2' := hp2
      have g2' := gate_of_reach u2 w2 hr2
      unfold Parent at h1' h2'
      unfold Gate at g1' g2'
      omega) hr2
  obtain ⟨u4,w4,hr4,hp4⟩ :=
    parent_of_reach u3 w3 (by
      have h1' := hp1
      have g1' := gate_of_reach u1 w1 hr1
      have h2' := hp2
      have g2' := gate_of_reach u2 w2 hr2
      have h3' := hp3
      have g3' := gate_of_reach u3 w3 hr3
      unfold Parent at h1' h2' h3'
      unfold Gate at g1' g2' g3'
      omega) hr3
  obtain ⟨u5,w5,hr5,hp5⟩ :=
    parent_of_reach u4 w4 (by
      have h1' := hp1
      have g1' := gate_of_reach u1 w1 hr1
      have h2' := hp2
      have g2' := gate_of_reach u2 w2 hr2
      have h3' := hp3
      have g3' := gate_of_reach u3 w3 hr3
      have h4' := hp4
      have g4' := gate_of_reach u4 w4 hr4
      unfold Parent at h1' h2' h3' h4'
      unfold Gate at g1' g2' g3' g4'
      omega) hr4
  obtain ⟨u6,w6,hr6,hp6⟩ :=
    parent_of_reach u5 w5 (by
      have h1' := hp1
      have g1' := gate_of_reach u1 w1 hr1
      have h2' := hp2
      have g2' := gate_of_reach u2 w2 hr2
      have h3' := hp3
      have g3' := gate_of_reach u3 w3 hr3
      have h4' := hp4
      have g4' := gate_of_reach u4 w4 hr4
      have h5' := hp5
      have g5' := gate_of_reach u5 w5 hr5
      unfold Parent at h1' h2' h3' h4' h5'
      unfold Gate at g1' g2' g3' g4' g5'
      omega) hr5
  obtain ⟨u7,w7,hr7,hp7⟩ :=
    parent_of_reach u6 w6 (by
      have h1' := hp1
      have g1' := gate_of_reach u1 w1 hr1
      have h2' := hp2
      have g2' := gate_of_reach u2 w2 hr2
      have h3' := hp3
      have g3' := gate_of_reach u3 w3 hr3
      have h4' := hp4
      have g4' := gate_of_reach u4 w4 hr4
      have h5' := hp5
      have g5' := gate_of_reach u5 w5 hr5
      have h6' := hp6
      have g6' := gate_of_reach u6 w6 hr6
      unfold Parent at h1' h2' h3' h4' h5' h6'
      unfold Gate at g1' g2' g3' g4' g5' g6'
      omega) hr6
  obtain ⟨u8,w8,hr8,hp8⟩ :=
    parent_of_reach u7 w7 (by
      have h1' := hp1
      have g1' := gate_of_reach u1 w1 hr1
      have h2' := hp2
      have g2' := gate_of_reach u2 w2 hr2
      have h3' := hp3
      have g3' := gate_of_reach u3 w3 hr3
      have h4' := hp4
      have g4' := gate_of_reach u4 w4 hr4
      have h5' := hp5
      have g5' := gate_of_reach u5 w5 hr5
      have h6' := hp6
      have g6' := gate_of_reach u6 w6 hr6
      have h7' := hp7
      have g7' := gate_of_reach u7 w7 hr7
      unfold Parent at h1' h2' h3' h4' h5' h6' h7'
      unfold Gate at g1' g2' g3' g4' g5' g6' g7'
      omega) hr7
  exact BB429RootExtendedArithmetic.branch13_q0mod8_no_eight
    t u1 w1 u2 w2 u3 w3 u4 w4 u5 w5 u6 w6 u7 w7 u8 w8 ht hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 (gate_of_reach u1 w1 hr1) (gate_of_reach u2 w2 hr2) (gate_of_reach u3 w3 hr3) (gate_of_reach u4 w4 hr4) (gate_of_reach u5 w5 hr5) (gate_of_reach u6 w6 hr6) (gate_of_reach u7 w7 hr7) (gate_of_reach u8 w8 hr8)

theorem branch13_q1mod8_unreachable (t : Nat) (ht : 1 ≤ t) :
    ¬ Reach (256*t+45) (512*t+87) := by
  intro h0
  obtain ⟨u1,w1,hr1,hp1⟩ :=
    parent_of_reach (256*t+45) (512*t+87) (by omega) h0
  obtain ⟨u2,w2,hr2,hp2⟩ :=
    parent_of_reach u1 w1 (by
      have h1' := hp1
      have g1' := gate_of_reach u1 w1 hr1
      unfold Parent at h1'
      unfold Gate at g1'
      omega) hr1
  obtain ⟨u3,w3,hr3,hp3⟩ :=
    parent_of_reach u2 w2 (by
      have h1' := hp1
      have g1' := gate_of_reach u1 w1 hr1
      have h2' := hp2
      have g2' := gate_of_reach u2 w2 hr2
      unfold Parent at h1' h2'
      unfold Gate at g1' g2'
      omega) hr2
  obtain ⟨u4,w4,hr4,hp4⟩ :=
    parent_of_reach u3 w3 (by
      have h1' := hp1
      have g1' := gate_of_reach u1 w1 hr1
      have h2' := hp2
      have g2' := gate_of_reach u2 w2 hr2
      have h3' := hp3
      have g3' := gate_of_reach u3 w3 hr3
      unfold Parent at h1' h2' h3'
      unfold Gate at g1' g2' g3'
      omega) hr3
  obtain ⟨u5,w5,hr5,hp5⟩ :=
    parent_of_reach u4 w4 (by
      have h1' := hp1
      have g1' := gate_of_reach u1 w1 hr1
      have h2' := hp2
      have g2' := gate_of_reach u2 w2 hr2
      have h3' := hp3
      have g3' := gate_of_reach u3 w3 hr3
      have h4' := hp4
      have g4' := gate_of_reach u4 w4 hr4
      unfold Parent at h1' h2' h3' h4'
      unfold Gate at g1' g2' g3' g4'
      omega) hr4
  obtain ⟨u6,w6,hr6,hp6⟩ :=
    parent_of_reach u5 w5 (by
      have h1' := hp1
      have g1' := gate_of_reach u1 w1 hr1
      have h2' := hp2
      have g2' := gate_of_reach u2 w2 hr2
      have h3' := hp3
      have g3' := gate_of_reach u3 w3 hr3
      have h4' := hp4
      have g4' := gate_of_reach u4 w4 hr4
      have h5' := hp5
      have g5' := gate_of_reach u5 w5 hr5
      unfold Parent at h1' h2' h3' h4' h5'
      unfold Gate at g1' g2' g3' g4' g5'
      omega) hr5
  obtain ⟨u7,w7,hr7,hp7⟩ :=
    parent_of_reach u6 w6 (by
      have h1' := hp1
      have g1' := gate_of_reach u1 w1 hr1
      have h2' := hp2
      have g2' := gate_of_reach u2 w2 hr2
      have h3' := hp3
      have g3' := gate_of_reach u3 w3 hr3
      have h4' := hp4
      have g4' := gate_of_reach u4 w4 hr4
      have h5' := hp5
      have g5' := gate_of_reach u5 w5 hr5
      have h6' := hp6
      have g6' := gate_of_reach u6 w6 hr6
      unfold Parent at h1' h2' h3' h4' h5' h6'
      unfold Gate at g1' g2' g3' g4' g5' g6'
      omega) hr6
  obtain ⟨u8,w8,hr8,hp8⟩ :=
    parent_of_reach u7 w7 (by
      have h1' := hp1
      have g1' := gate_of_reach u1 w1 hr1
      have h2' := hp2
      have g2' := gate_of_reach u2 w2 hr2
      have h3' := hp3
      have g3' := gate_of_reach u3 w3 hr3
      have h4' := hp4
      have g4' := gate_of_reach u4 w4 hr4
      have h5' := hp5
      have g5' := gate_of_reach u5 w5 hr5
      have h6' := hp6
      have g6' := gate_of_reach u6 w6 hr6
      have h7' := hp7
      have g7' := gate_of_reach u7 w7 hr7
      unfold Parent at h1' h2' h3' h4' h5' h6' h7'
      unfold Gate at g1' g2' g3' g4' g5' g6' g7'
      omega) hr7
  exact BB429RootExtendedArithmetic.branch13_q1mod8_no_eight
    t u1 w1 u2 w2 u3 w3 u4 w4 u5 w5 u6 w6 u7 w7 u8 w8 ht hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 (gate_of_reach u1 w1 hr1) (gate_of_reach u2 w2 hr2) (gate_of_reach u3 w3 hr3) (gate_of_reach u4 w4 hr4) (gate_of_reach u5 w5 hr5) (gate_of_reach u6 w6 hr6) (gate_of_reach u7 w7 hr7) (gate_of_reach u8 w8 hr8)

theorem branch13_q5mod16_unreachable (t : Nat) (ht : 1 ≤ t) :
    ¬ Reach (512*t+173) (1024*t+343) := by
  intro h0
  obtain ⟨u1,w1,hr1,hp1⟩ :=
    parent_of_reach (512*t+173) (1024*t+343) (by omega) h0
  obtain ⟨u2,w2,hr2,hp2⟩ :=
    parent_of_reach u1 w1 (by
      have h1' := hp1
      have g1' := gate_of_reach u1 w1 hr1
      unfold Parent at h1'
      unfold Gate at g1'
      omega) hr1
  obtain ⟨u3,w3,hr3,hp3⟩ :=
    parent_of_reach u2 w2 (by
      have h1' := hp1
      have g1' := gate_of_reach u1 w1 hr1
      have h2' := hp2
      have g2' := gate_of_reach u2 w2 hr2
      unfold Parent at h1' h2'
      unfold Gate at g1' g2'
      omega) hr2
  obtain ⟨u4,w4,hr4,hp4⟩ :=
    parent_of_reach u3 w3 (by
      have h1' := hp1
      have g1' := gate_of_reach u1 w1 hr1
      have h2' := hp2
      have g2' := gate_of_reach u2 w2 hr2
      have h3' := hp3
      have g3' := gate_of_reach u3 w3 hr3
      unfold Parent at h1' h2' h3'
      unfold Gate at g1' g2' g3'
      omega) hr3
  obtain ⟨u5,w5,hr5,hp5⟩ :=
    parent_of_reach u4 w4 (by
      have h1' := hp1
      have g1' := gate_of_reach u1 w1 hr1
      have h2' := hp2
      have g2' := gate_of_reach u2 w2 hr2
      have h3' := hp3
      have g3' := gate_of_reach u3 w3 hr3
      have h4' := hp4
      have g4' := gate_of_reach u4 w4 hr4
      unfold Parent at h1' h2' h3' h4'
      unfold Gate at g1' g2' g3' g4'
      omega) hr4
  obtain ⟨u6,w6,hr6,hp6⟩ :=
    parent_of_reach u5 w5 (by
      have h1' := hp1
      have g1' := gate_of_reach u1 w1 hr1
      have h2' := hp2
      have g2' := gate_of_reach u2 w2 hr2
      have h3' := hp3
      have g3' := gate_of_reach u3 w3 hr3
      have h4' := hp4
      have g4' := gate_of_reach u4 w4 hr4
      have h5' := hp5
      have g5' := gate_of_reach u5 w5 hr5
      unfold Parent at h1' h2' h3' h4' h5'
      unfold Gate at g1' g2' g3' g4' g5'
      omega) hr5
  obtain ⟨u7,w7,hr7,hp7⟩ :=
    parent_of_reach u6 w6 (by
      have h1' := hp1
      have g1' := gate_of_reach u1 w1 hr1
      have h2' := hp2
      have g2' := gate_of_reach u2 w2 hr2
      have h3' := hp3
      have g3' := gate_of_reach u3 w3 hr3
      have h4' := hp4
      have g4' := gate_of_reach u4 w4 hr4
      have h5' := hp5
      have g5' := gate_of_reach u5 w5 hr5
      have h6' := hp6
      have g6' := gate_of_reach u6 w6 hr6
      unfold Parent at h1' h2' h3' h4' h5' h6'
      unfold Gate at g1' g2' g3' g4' g5' g6'
      omega) hr6
  obtain ⟨u8,w8,hr8,hp8⟩ :=
    parent_of_reach u7 w7 (by
      have h1' := hp1
      have g1' := gate_of_reach u1 w1 hr1
      have h2' := hp2
      have g2' := gate_of_reach u2 w2 hr2
      have h3' := hp3
      have g3' := gate_of_reach u3 w3 hr3
      have h4' := hp4
      have g4' := gate_of_reach u4 w4 hr4
      have h5' := hp5
      have g5' := gate_of_reach u5 w5 hr5
      have h6' := hp6
      have g6' := gate_of_reach u6 w6 hr6
      have h7' := hp7
      have g7' := gate_of_reach u7 w7 hr7
      unfold Parent at h1' h2' h3' h4' h5' h6' h7'
      unfold Gate at g1' g2' g3' g4' g5' g6' g7'
      omega) hr7
  obtain ⟨u9,w9,hr9,hp9⟩ :=
    parent_of_reach u8 w8 (by
      have h1' := hp1
      have g1' := gate_of_reach u1 w1 hr1
      have h2' := hp2
      have g2' := gate_of_reach u2 w2 hr2
      have h3' := hp3
      have g3' := gate_of_reach u3 w3 hr3
      have h4' := hp4
      have g4' := gate_of_reach u4 w4 hr4
      have h5' := hp5
      have g5' := gate_of_reach u5 w5 hr5
      have h6' := hp6
      have g6' := gate_of_reach u6 w6 hr6
      have h7' := hp7
      have g7' := gate_of_reach u7 w7 hr7
      have h8' := hp8
      have g8' := gate_of_reach u8 w8 hr8
      unfold Parent at h1' h2' h3' h4' h5' h6' h7' h8'
      unfold Gate at g1' g2' g3' g4' g5' g6' g7' g8'
      omega) hr8
  exact BB429RootExtendedArithmetic.branch13_q5mod16_no_nine
    t u1 w1 u2 w2 u3 w3 u4 w4 u5 w5 u6 w6 u7 w7 u8 w8 u9 w9 ht hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 (gate_of_reach u1 w1 hr1) (gate_of_reach u2 w2 hr2) (gate_of_reach u3 w3 hr3) (gate_of_reach u4 w4 hr4) (gate_of_reach u5 w5 hr5) (gate_of_reach u6 w6 hr6) (gate_of_reach u7 w7 hr7) (gate_of_reach u8 w8 hr8) (gate_of_reach u9 w9 hr9)

theorem branch15_q2mod8_unreachable (t : Nat) (ht : 1 ≤ t) :
    ¬ Reach (256*t+79) (512*t+155) := by
  intro h0
  obtain ⟨u1,w1,hr1,hp1⟩ :=
    parent_of_reach (256*t+79) (512*t+155) (by omega) h0
  obtain ⟨u2,w2,hr2,hp2⟩ :=
    parent_of_reach u1 w1 (by
      have h1' := hp1
      have g1' := gate_of_reach u1 w1 hr1
      unfold Parent at h1'
      unfold Gate at g1'
      omega) hr1
  obtain ⟨u3,w3,hr3,hp3⟩ :=
    parent_of_reach u2 w2 (by
      have h1' := hp1
      have g1' := gate_of_reach u1 w1 hr1
      have h2' := hp2
      have g2' := gate_of_reach u2 w2 hr2
      unfold Parent at h1' h2'
      unfold Gate at g1' g2'
      omega) hr2
  obtain ⟨u4,w4,hr4,hp4⟩ :=
    parent_of_reach u3 w3 (by
      have h1' := hp1
      have g1' := gate_of_reach u1 w1 hr1
      have h2' := hp2
      have g2' := gate_of_reach u2 w2 hr2
      have h3' := hp3
      have g3' := gate_of_reach u3 w3 hr3
      unfold Parent at h1' h2' h3'
      unfold Gate at g1' g2' g3'
      omega) hr3
  obtain ⟨u5,w5,hr5,hp5⟩ :=
    parent_of_reach u4 w4 (by
      have h1' := hp1
      have g1' := gate_of_reach u1 w1 hr1
      have h2' := hp2
      have g2' := gate_of_reach u2 w2 hr2
      have h3' := hp3
      have g3' := gate_of_reach u3 w3 hr3
      have h4' := hp4
      have g4' := gate_of_reach u4 w4 hr4
      unfold Parent at h1' h2' h3' h4'
      unfold Gate at g1' g2' g3' g4'
      omega) hr4
  obtain ⟨u6,w6,hr6,hp6⟩ :=
    parent_of_reach u5 w5 (by
      have h1' := hp1
      have g1' := gate_of_reach u1 w1 hr1
      have h2' := hp2
      have g2' := gate_of_reach u2 w2 hr2
      have h3' := hp3
      have g3' := gate_of_reach u3 w3 hr3
      have h4' := hp4
      have g4' := gate_of_reach u4 w4 hr4
      have h5' := hp5
      have g5' := gate_of_reach u5 w5 hr5
      unfold Parent at h1' h2' h3' h4' h5'
      unfold Gate at g1' g2' g3' g4' g5'
      omega) hr5
  obtain ⟨u7,w7,hr7,hp7⟩ :=
    parent_of_reach u6 w6 (by
      have h1' := hp1
      have g1' := gate_of_reach u1 w1 hr1
      have h2' := hp2
      have g2' := gate_of_reach u2 w2 hr2
      have h3' := hp3
      have g3' := gate_of_reach u3 w3 hr3
      have h4' := hp4
      have g4' := gate_of_reach u4 w4 hr4
      have h5' := hp5
      have g5' := gate_of_reach u5 w5 hr5
      have h6' := hp6
      have g6' := gate_of_reach u6 w6 hr6
      unfold Parent at h1' h2' h3' h4' h5' h6'
      unfold Gate at g1' g2' g3' g4' g5' g6'
      omega) hr6
  obtain ⟨u8,w8,hr8,hp8⟩ :=
    parent_of_reach u7 w7 (by
      have h1' := hp1
      have g1' := gate_of_reach u1 w1 hr1
      have h2' := hp2
      have g2' := gate_of_reach u2 w2 hr2
      have h3' := hp3
      have g3' := gate_of_reach u3 w3 hr3
      have h4' := hp4
      have g4' := gate_of_reach u4 w4 hr4
      have h5' := hp5
      have g5' := gate_of_reach u5 w5 hr5
      have h6' := hp6
      have g6' := gate_of_reach u6 w6 hr6
      have h7' := hp7
      have g7' := gate_of_reach u7 w7 hr7
      unfold Parent at h1' h2' h3' h4' h5' h6' h7'
      unfold Gate at g1' g2' g3' g4' g5' g6' g7'
      omega) hr7
  exact BB429RootExtendedArithmetic.branch15_q2mod8_no_eight
    t u1 w1 u2 w2 u3 w3 u4 w4 u5 w5 u6 w6 u7 w7 u8 w8 ht hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 (gate_of_reach u1 w1 hr1) (gate_of_reach u2 w2 hr2) (gate_of_reach u3 w3 hr3) (gate_of_reach u4 w4 hr4) (gate_of_reach u5 w5 hr5) (gate_of_reach u6 w6 hr6) (gate_of_reach u7 w7 hr7) (gate_of_reach u8 w8 hr8)


#print axioms branch13_q0mod8_unreachable
#print axioms branch13_q1mod8_unreachable
#print axioms branch13_q5mod16_unreachable
#print axioms branch15_q2mod8_unreachable
end BB429RootExtendedSource
