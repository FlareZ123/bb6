import Agent8GateRepulsionSource

/-!
Full five-branch exact-source two-step gate repulsion for Cryptids BB6 #623.
The quantified claim excludes a terminal daughter for any successful
positive-even-first-coordinate parent satisfying explicit branch budgets.
The authentic blank root is not proved to satisfy these budgets for all time.
-/

namespace BB6.Agent8GateCompleteSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent8GateRepulsionSource

/-- Odd right-of-diagonal branch: B-drain forces a right-dominated
successor whenever the ternary length and linear room permit it. -/
theorem odd_left_diagonal_repulsion (a d k aa dd : Nat)
    (ha : 0<a) (hd : d%2=1) (hleft : d+5≤a)
    (hpow : d+3 < 3^k) (hroom : 2*a+2*k ≤ 5*d+16)
    (hstep : highLevelNext (.D a d) = some (.D aa dd)) :
    2*aa+8 ≤ dd := by
  have h0 : a ≠ 0 := by omega
  have h1 : d%2=1 ∧ a≥d+5 := ⟨hd,by omega⟩
  simp only [highLevelNext, if_neg h0, if_pos h1] at hstep
  have hf := drainB_first_le_pow k (a-d-5) (d+3) 5 aa dd hpow hstep
  have ht := BB6.Agent8BudgetSource.drainB_d3 (d+3) (a-d-5) 5 aa dd hstep
  omega

/-- Even right-of-diagonal branch. -/
theorem even_left_diagonal_repulsion (a d k aa dd : Nat)
    (ha : 0<a) (hd : d%2=0) (hleft : d+3≤a)
    (hpow : d+2 < 3^k) (hroom : 2*a+2*k ≤ 5*d+4)
    (hstep : highLevelNext (.D a d) = some (.D aa dd)) :
    2*aa+8 ≤ dd := by
  have h0 : a ≠ 0 := by omega
  have h1 : ¬(d%2=1 ∧ a≥d+5) := by omega
  have h2 : d%2=0 ∧ a≥d+3 := ⟨hd,by omega⟩
  simp only [highLevelNext, if_neg h0, if_neg h1, if_pos h2] at hstep
  have hf := drainB_first_le_pow k (a-d-2) (d+2) 2 aa dd hpow hstep
  have ht := BB6.Agent8BudgetSource.drainB_d3 (d+2) (a-d-2) 2 aa dd hstep
  omega

/-- Exceptional middle branch with a=d+2. -/
theorem gap_two_diagonal_repulsion (a d k aa dd : Nat)
    (he : a%2=0) (hd : d%2=0) (hgap : a=d+2)
    (hpow : a<3^k) (hroom : 2*k+6 ≤ 3*a)
    (hstep : highLevelNext (.D a d) = some (.D aa dd)) :
    2*aa+8 ≤ dd := by
  have h0 : a ≠ 0 := by omega
  have h1 : ¬(d%2=1 ∧ a≥d+5) := by omega
  have h2 : ¬(d%2=0 ∧ a≥d+3) := by omega
  have h3 : a%2 ≠ 1 := by omega
  simp only [highLevelNext, if_neg h0, if_neg h1, if_neg h2,
    if_neg h3, if_pos hgap] at hstep
  have hf := drainB_first_le_pow k 0 a 2 aa dd hpow hstep
  have ht := BB6.Agent8BudgetSource.drainB_d3 a 0 2 aa dd hstep
  omega

/-- The five source branches for positive even first coordinate, each
with a sufficient ternary/logarithmic budget. -/
def gateBudget (a d k : Nat) : Prop :=
  (d%2=1 ∧ a<d+5 ∧ a-1<3^k ∧ 2*d+2*k+16≤5*a) ∨
  (d%2=1 ∧ d+5≤a ∧ d+3<3^k ∧ 2*a+2*k≤5*d+16) ∨
  (d%2=0 ∧ a≤d ∧ a<3^k ∧ 2*d+2*k+7≤4*a) ∨
  (d%2=0 ∧ a=d+2 ∧ a<3^k ∧ 2*k+6≤3*a) ∨
  (d%2=0 ∧ d+3≤a ∧ d+2<3^k ∧ 2*a+2*k≤5*d+4)

/-- All successful budgeted near-diagonal returns are forcibly
right-dominated: 2*aa+8 <= dd. -/
theorem gate_budget_repulsion (a d k aa dd : Nat)
    (ha : 0<a) (he : a%2=0) (hg : gateBudget a d k)
    (hs : highLevelNext (.D a d) = some (.D aa dd)) :
    2*aa+8 ≤ dd := by
  unfold gateBudget at hg
  rcases hg with h1|h2|h3|h4|h5
  · rcases h1 with ⟨hd,hle,hpow,hroom⟩
    exact BB6.Agent8GateRepulsionSource.odd_diagonal_repulsion
      a d k aa dd ha he hd hle hpow hroom hs
  · rcases h2 with ⟨hd,hle,hpow,hroom⟩
    exact odd_left_diagonal_repulsion a d k aa dd ha hd hle hpow hroom hs
  · rcases h3 with ⟨hd,hle,hpow,hroom⟩
    exact BB6.Agent8GateRepulsionSource.even_diagonal_repulsion
      a d k aa dd ha he hd hle hpow hroom hs
  · rcases h4 with ⟨hd,hgap,hpow,hroom⟩
    exact gap_two_diagonal_repulsion a d k aa dd he hd hgap hpow hroom hs
  · rcases h5 with ⟨hd,hle,hpow,hroom⟩
    exact even_left_diagonal_repulsion a d k aa dd ha hd hle hpow hroom hs

/-- Full five-branch source guarantee for a second successful return. -/
theorem gate_budget_two_step (a d k aa dd : Nat)
    (ha : 0<a) (he : a%2=0) (hg : gateBudget a d k)
    (hs : highLevelNext (.D a d) = some (.D aa dd)) :
    ∃bb ee, highLevelNext (.D aa dd) = some (.D bb ee) := by
  have hr := gate_budget_repulsion a d k aa dd ha he hg hs
  have hp := BB6.Agent49ParitySource.next_preserves_even a d aa dd he hs
  exact BB6.Agent8GateRepulsionSource.right_dominated_safe aa dd hp hr

/-- No successful budgeted parent can lead directly to a terminal state. -/
theorem gate_budget_excludes_terminal_parent (a d k aa dd : Nat)
    (ha : 0<a) (he : a%2=0) (hg : gateBudget a d k)
    (hs : highLevelNext (.D a d) = some (.D aa dd)) :
    highLevelNext (.D aa dd) ≠ none := by
  obtain ⟨bb,ee,hnext⟩ := gate_budget_two_step a d k aa dd ha he hg hs
  simp [hnext]

#print axioms odd_left_diagonal_repulsion
#print axioms even_left_diagonal_repulsion
#print axioms gap_two_diagonal_repulsion
#print axioms gate_budget_repulsion
#print axioms gate_budget_two_step
#print axioms gate_budget_excludes_terminal_parent
end BB6.Agent8GateCompleteSource
