import Agent8DigitChargeSource

/-!
Four exact original-source branches of the #623 accelerated return,
with all ternary digit corrections explicitly represented by digitCode.
These statements apply directly to the original physical machine's
accelerated semantics, but none decides its blank-root survival.
-/
namespace BB6.Agent8RootDigitChargeSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent8DigitChargeSource

theorem left_odd_charge (a d aa dd : Nat)
  (hpos : 0<a) (hodd : d%2=1) (hl : d+5≤a)
  (h : highLevelNext (.D a d)=some (.D aa dd)) :
  ∃ c, digitCode (a-d-5) (d+3) = some (aa,c) ∧ dd = 3*d+14+c := by
  have hz : a≠0 := by omega
  have hb : d%2=1 ∧ a≥d+5 := ⟨hodd,hl⟩
  have hraw : drainB (a-d-5) (d+3) 5 = some (.D aa dd) := by
    simpa only [highLevelNext,if_neg hz,if_pos hb] using h
  obtain ⟨c,hc,hdd⟩ := drainB_charge_witness (a-d-5) (d+3) 5 aa dd hraw
  exact ⟨c,hc,by omega⟩

theorem left_even_charge (a d aa dd : Nat)
  (hpos : 0<a) (heven : d%2=0) (hl : d+3≤a)
  (h : highLevelNext (.D a d)=some (.D aa dd)) :
  ∃ c, digitCode (a-d-2) (d+2) = some (aa,c) ∧ dd = 3*d+8+c := by
  have hz : a≠0 := by omega
  have hnodd : ¬ (d%2=1 ∧ a≥d+5) := by omega
  have hb : d%2=0 ∧ a≥d+3 := ⟨heven,hl⟩
  have hraw : drainB (a-d-2) (d+2) 2 = some (.D aa dd) := by
    simpa only [highLevelNext,if_neg hz,if_neg hnodd,if_pos hb] using h
  obtain ⟨c,hc,hdd⟩ := drainB_charge_witness (a-d-2) (d+2) 2 aa dd hraw
  exact ⟨c,hc,by omega⟩

theorem right_odd_charge (a d aa dd : Nat)
  (hpos : 0<a) (heven : a%2=0) (hodd : d%2=1) (hr : a≤d)
  (h : highLevelNext (.D a d)=some (.D aa dd)) :
  ∃ c, digitCode (d+4-a) (a-1) = some (aa,c) ∧ dd = 3*a+c := by
  have hz : a≠0 := by omega
  have hnotleft : ¬ (d%2=1 ∧ a≥d+5) := by omega
  have hnoteven : ¬ (d%2=0 ∧ a≥d+3) := by omega
  have hnotpar : a%2≠1 := by omega
  have hnotdiag : a≠d+2 := by omega
  have hraw : drainB (d+4-a) (a-1) 3 = some (.D aa dd) := by
    simpa only [highLevelNext,if_neg hz,if_neg hnotleft,if_neg hnoteven,if_neg hnotpar,if_neg hnotdiag,if_pos hodd] using h
  obtain ⟨c,hc,hdd⟩ := drainB_charge_witness (d+4-a) (a-1) 3 aa dd hraw
  exact ⟨c,hc,by omega⟩

theorem diagonal_charge (a d aa dd : Nat)
  (heven : a%2=0) (hevend : d%2=0) (hdiag : a=d+2)
  (h : highLevelNext (.D a d)=some (.D aa dd)) :
  ∃ c, digitCode 0 a = some (aa,c) ∧ dd = 3*a+2+c := by
  have hz : a≠0 := by omega
  have hnotleft : ¬ (d%2=1 ∧ a≥d+5) := by omega
  have hnoteven : ¬ (d%2=0 ∧ a≥d+3) := by omega
  have hnotpar : a%2≠1 := by omega
  have hraw : drainB 0 a 2 = some (.D aa dd) := by
    simpa only [highLevelNext,if_neg hz,if_neg hnotleft,if_neg hnoteven,if_neg hnotpar,if_pos hdiag] using h
  obtain ⟨c,hc,hdd⟩ := drainB_charge_witness 0 a 2 aa dd hraw
  exact ⟨c,hc,by omega⟩

#print axioms left_odd_charge
#print axioms left_even_charge
#print axioms right_odd_charge
#print axioms diagonal_charge
end BB6.Agent8RootDigitChargeSource
