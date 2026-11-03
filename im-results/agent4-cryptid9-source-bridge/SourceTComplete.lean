import SourceGate
import STTransferResidues

namespace Agent4TComplete
open BusyBeaver.M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB
open BB6.Agent9STResidues

theorem t_none_iff_tag (m : Nat) :
    highLevelNext (.T m) = none ↔ tTag m = 5 := by
  have hf (x : Nat) : 2*(2*x) = 4*x := by omega
  simp only [highLevelNext, tTag, g, g2, g3, g4, hf]
  by_cases h0 : m%3=0
  · simp [h0]
  simp only [ite_eq_right h0]
  by_cases h1 : m%3=2
  · simp [h0,h1]
  simp only [ite_eq_right h1]
  by_cases h2 : (4*(m/3)+7)%3=0
  · simp [h0,h1,h2]
  simp only [ite_eq_right h2]
  by_cases h3 : (4*(m/3)+7)%3=2
  · simp [h0,h1,h2,h3]
  simp only [ite_eq_right h3]
  by_cases h4 : (4*((4*(m/3)+7)/3)+7)%3=0
  · simp [h0,h1,h2,h3,h4]
  simp only [ite_eq_right h4]
  by_cases h5 : (4*((4*(m/3)+7)/3)+7)%3=2
  · simp [h0,h1,h2,h3,h4,h5]
  simp only [ite_eq_right h5]
  by_cases h6 : (4*((4*((4*(m/3)+7)/3)+7)/3)+7)%3≠0
  · simp [h0,h1,h2,h3,h4,h5,h6]
  simp only [ite_eq_right h6]
  by_cases h7 : (4*((4*((4*((4*(m/3)+7)/3)+7)/3)+7)/3)+6)%3=1
  · simp [h0,h1,h2,h3,h4,h5,h6,h7]
  by_cases h8 : (4*((4*((4*((4*(m/3)+7)/3)+7)/3)+7)/3)+6)%3=0
  · simp [h2,h3,h4,h5,h6,h7,h8]
  · simp [h2,h3,h4,h5,h6,h7,h8]

theorem t_none_seven_residues (m : Nat) :
    highLevelNext (.T m) = none ↔
    m%243=10 ∨ m%243=37 ∨ m%243=64 ∨ m%243=91 ∨
    m%243=145 ∨ m%243=172 ∨ m%243=226 := by
  exact (t_none_iff_tag m).trans (immediate_halt_seven_residues m)

#print axioms t_none_iff_tag
#print axioms t_none_seven_residues
end Agent4TComplete
