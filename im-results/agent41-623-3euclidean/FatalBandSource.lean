import DrainImageAP
import DrainImageSource

namespace BB6.Agent41FatalBand
open BB6.Agent41DrainImageDecoder
open BB6.Agent41DrainImageSource
open BB6.Agent49FlatDrainSource
open BB6.Agent49InverseWindowSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

def terminalFirst (d : Nat) : Nat := if d%2=0 then d+2 else d+5

theorem terminal_first_even (d : Nat) : (terminalFirst d)%2=0 := by
  unfold terminalFirst
  split <;> omega

theorem terminal_of_mod (d : Nat) (hd : d%6=1 ∨ d%6=2) :
    highLevelNext (.D (terminalFirst d) d)= none := by
  unfold terminalFirst
  by_cases h : d%2=0
  · rw [if_pos h]
    have hrep : d+2=3*((d+2)/3)+1 := by omega
    simp only [highLevelNext,if_neg (show d+2≠0 by omega),
      if_neg (show ¬(d%2=1 ∧ d+2≥ d+5) by omega),
      if_neg (show ¬(d%2=0 ∧ d+2≥ d+3) by omega),
      if_neg (show (d+2)%2≠1 by omega),if_pos rfl]
    rw [hrep]
    exact drain_three_one_zero _ _
  · rw [if_neg h]
    have hrep : d+3=3*((d+3)/3)+1 := by omega
    simp only [highLevelNext,if_neg (show d+5≠0 by omega),
      if_pos (show d%2=1 ∧ d+5≥ d+5 by omega),
      show d+5-d-5=0 by omega]
    rw [hrep]
    exact drain_three_one_zero _ _

private theorem twice_le_pow_two (n : Nat) : 2*n≤2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.pow_succ]
    by_cases h : n=0
    · subst n; decide
    · omega

theorem terminal_budget (d : Nat) (hd : 0 < d) :
    2*inverseBudget d≤ terminalFirst d := by
  have h := Nat.log2_self_le (show d≠0 by omega)
  have ht := twice_le_pow_two d.log2
  unfold inverseBudget terminalFirst
  split <;> omega

/-- In every band, disjoint triples of candidate rows contain an actual
synthetic halter with no authentic predecessor. -/
theorem excluded_terminal_band (k t : Nat) (hk : 9*t+4≤ k) :
    let d0 := 9*tau k+18*t+(if k%2=0 then 8 else 4)
    ∃ r, r≤2 ∧
      let d := d0+6*r
      highLevelNext (.D (terminalFirst d) d)= none ∧
      (∀ a c, highLevelNext (.D a c)≠some (.D (terminalFirst d) d)) ∧
      (∀ n, BB6.Agent49ParitySource.run n≠some (.D (terminalFirst d) d)) := by
  dsimp
  let j := 9*t+(if k%2=0 then 3 else 2)
  let d0 := 9*tau k+18*t+(if k%2=0 then 8 else 4)
  have h1 : 1≤ j := by dsimp [j]; split <;> omega
  have h2 : j+6≤ k+5 := by dsimp [j]; split <;> omega
  have hj : 9*tau k+2*j+(if k%2=0 then 2 else 0)= d0 := by
    dsimp [j,d0]
    by_cases h : k%2=0 <;> simp [h] <;> omega
  have hb := blocked_band_six excessLaws k j (by omega) h1 h2
  dsimp at hb
  rw [hj] at hb
  obtain ⟨r,hr,hb'⟩ : ∃ r, r≤2 ∧ blocked (d0+6*r) := by
    rcases hb with h|h|h
    · exact ⟨0,by decide,by simpa using h⟩
    · exact ⟨1,by decide,by simpa using h⟩
    · exact ⟨2,by decide,by simpa using h⟩
  refine ⟨r,hr,?_⟩
  let d := d0+6*r
  have hp := tau_parity k
  have hmod : d%6=1 ∨ d%6=2 := by
    dsimp [d,d0]
    by_cases h : k%2=0 <;> simp [h] <;> omega
  have ht := tau_mono (show 2≤ k by omega)
  have ht' : tau 2=4 := by decide
  rw [ht'] at ht
  have hd : 14 < d := by dsimp [d,d0]; split <;> omega
  have hbudget := terminal_budget d (by omega)
  exact ⟨terminal_of_mod d hmod,
    fun a c => no_parent_of_blocked a c (terminalFirst d) d hd hbudget hb',
    fun n => root_excluded_of_blocked n (terminalFirst d) d hd hbudget hb'⟩

def excludedRow (c : Nat) : Nat :=
  terminalRow BB6.Agent49CorrectionGrowth.excess c

theorem excluded_row_spec (c : Nat) :
    let d := excludedRow c
    let b := 19683*c+29523
    d≤3*b+4*(b.log2+1)+20 ∧ d%2=(c+1)%2 ∧
    (d%6=1 ∨ d%6=2) ∧
    highLevelNext (.D (terminalFirst d) d)= none ∧
    (∀ a e, highLevelNext (.D a e)≠some (.D (terminalFirst d) d)) ∧
    (∀ n, BB6.Agent49ParitySource.run n≠some (.D (terminalFirst d) d)) := by
  dsimp [excludedRow]
  obtain ⟨h0,_,hb,hpar,hmod,hblocked⟩ := terminalRow_spec excessLaws c
  let d := terminalRow BB6.Agent49CorrectionGrowth.excess c
  have hF : 3*(19683*c+29523)≤ image BB6.Agent49CorrectionGrowth.excess (19683*c+29523) := by
    unfold image; omega
  have hd : 14 < d := by dsimp [d]; omega
  have hbudget := terminal_budget d (by omega)
  exact ⟨hb,hpar,hmod,terminal_of_mod d hmod,
    fun a e => no_parent_of_blocked a e (terminalFirst d) d hd hbudget hblocked,
    fun n => root_excluded_of_blocked n (terminalFirst d) d hd hbudget hblocked⟩

theorem excluded_row_injective : ∀ c c', excludedRow c= excludedRow c' → c= c' :=
  terminalRow_injective excessLaws

#print axioms excluded_row_spec
#print axioms excluded_row_injective
#print axioms terminal_of_mod
#print axioms terminal_budget
#print axioms excluded_terminal_band
end BB6.Agent41FatalBand
