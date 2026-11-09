import Agent49ThirdNinefoldSource

/-!
Two additional four-digit neutral contractions for the unchanged Cryptids #623
B-drain. They lie outside all nine compositions of residues 0,6,8 mod 9.
Paired with the previous three-digit alphabet they give 11 distinct exact
neutral residues modulo 81, all for arbitrary first counter and including
complete failing computations. No blank-origin orbit decision is claimed.
-/
namespace BB6.Agent49Eleven81Source
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49FlatDrainSource
open BB6.Agent49ThirdNinefoldSource

/-- A new primitive 81-adic neutral digit at residue 30. -/
theorem drain_81_thirty (a b d : Nat) :
    drainB a (81*b+30) d = drainB a b (d+240*b+96) := by
  have h1 : 81*b+30 = 3*(27*b+10) := by omega
  rw [h1, drain_three a (27*b+10) d (by omega)]
  have h2 : 27*b+10-1=3*(9*b+3) := by omega
  rw [h2, drain_three (a+1) (9*b+3) (d+6*(27*b+10)+3) (by omega)]
  have h3 : 9*b+3-1=3*(3*b)+2 := by omega
  rw [h3, drain_three_two (a+1+1) (3*b)
        (d+6*(27*b+10)+3+6*(9*b+3)+3) (by omega)]
  rw [drain_three_one (a+1+1-1) b
        (d+6*(27*b+10)+3+6*(9*b+3)+3+6*(3*b)+5) (by omega)]
  congr 1 <;> omega

/-- The independent residue-48 primitive follows a different carry path. -/
theorem drain_81_fortyeight (a b d : Nat) :
    drainB a (81*b+48) d = drainB a b (d+240*b+152) := by
  have h1 : 81*b+48=3*(27*b+16) := by omega
  rw [h1, drain_three a (27*b+16) d (by omega)]
  have h2 : 27*b+16-1=3*(9*b+5) := by omega
  rw [h2, drain_three (a+1) (9*b+5) (d+6*(27*b+16)+3) (by omega)]
  have h3 : 9*b+5-1=3*(3*b+1)+1 := by omega
  rw [h3, drain_three_one (a+1+1) (3*b+1)
        (d+6*(27*b+16)+3+6*(9*b+5)+3) (by omega)]
  rw [drain_three_one (a+1+1-1) b
        (d+6*(27*b+16)+3+6*(9*b+5)+3+6*(3*b+1)+7) (by omega)]
  congr 1 <;> omega

#print axioms drain_81_thirty
#print axioms drain_81_fortyeight
end BB6.Agent49Eleven81Source
