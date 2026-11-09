import Agent8DrainMassCocycleSource

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
  (hpos : 0<a) (heven : a%2=0) (hodd : d%2=1) (hr : a<d+5)
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


/-- Authentic far-left odd branch: exact joint-mass gain d+9+e. -/
theorem left_odd_mass (a d aa dd : Nat)
  (hpos : 0<a) (hodd : d%2=1) (hl : d+5≤a)
  (h : highLevelNext (.D a d)=some (.D aa dd)) :
  ∃ e, excessMass (a-d-5) (d+3)=some e ∧ aa+dd=a+2*d+9+e := by
  obtain ⟨c,hc,hdd⟩ := left_odd_charge a d aa dd hpos hodd hl h
  have hm := code_mass (d+3) (a-d-5)
  rw [hc] at hm
  cases he : excessMass (a-d-5) (d+3) with
  | none => simp [he] at hm
  | some e =>
    simp only [he,Option.map_some,Option.some.injEq] at hm
    exact ⟨e,rfl,by omega⟩

/-- Authentic far-left even branch: exact joint-mass gain d+6+e. -/
theorem left_even_mass (a d aa dd : Nat)
  (hpos : 0<a) (heven : d%2=0) (hl : d+3≤a)
  (h : highLevelNext (.D a d)=some (.D aa dd)) :
  ∃ e, excessMass (a-d-2) (d+2)=some e ∧ aa+dd=a+2*d+6+e := by
  obtain ⟨c,hc,hdd⟩ := left_even_charge a d aa dd hpos heven hl h
  have hm := code_mass (d+2) (a-d-2)
  rw [hc] at hm
  cases he : excessMass (a-d-2) (d+2) with
  | none => simp [he] at hm
  | some e =>
    simp only [he,Option.map_some,Option.some.injEq] at hm
    exact ⟨e,rfl,by omega⟩

/-- Authentic right-side odd branch: exact joint-mass gain a+4+e. -/
theorem right_odd_mass (a d aa dd : Nat)
  (hpos : 0<a) (heven : a%2=0) (hodd : d%2=1) (hr : a<d+5)
  (h : highLevelNext (.D a d)=some (.D aa dd)) :
  ∃ e, excessMass (d+4-a) (a-1)=some e ∧ aa+dd=d+2*a+4+e := by
  obtain ⟨c,hc,hdd⟩ := right_odd_charge a d aa dd hpos heven hodd hr h
  have hm := code_mass (a-1) (d+4-a)
  rw [hc] at hm
  cases he : excessMass (d+4-a) (a-1) with
  | none => simp [he] at hm
  | some e =>
    simp only [he,Option.map_some,Option.some.injEq] at hm
    exact ⟨e,rfl,by omega⟩

/-- Authentic even diagonal branch: exact joint mass 3a+2+e. -/
theorem diagonal_mass (a d aa dd : Nat)
  (heven : a%2=0) (hevend : d%2=0) (hdiag : a=d+2)
  (h : highLevelNext (.D a d)=some (.D aa dd)) :
  ∃ e, excessMass 0 a=some e ∧ aa+dd=3*a+2+e := by
  obtain ⟨c,hc,hdd⟩ := diagonal_charge a d aa dd heven hevend hdiag h
  have hm := code_mass a 0
  rw [hc] at hm
  cases he : excessMass 0 a with
  | none => simp [he] at hm
  | some e =>
    simp only [he,Option.map_some,Option.some.injEq] at hm
    exact ⟨e,rfl,by omega⟩

/-- The complete right-even evaluator branch. Unlike the direct-drain
branches, the intrinsic digit charge uses the output of the original
evalA call. It has exactly the physical source's success criterion. -/
theorem right_even_last_charge (a d aa dd : Nat)
  (hpos : 0<a) (heven : a%2=0) (hdeven : d%2=0) (hr : a≤d)
  (h : highLevelNext (.D a d)=some (.D aa dd)) :
  ∃ x b m c, evalA (d+1-a) a (2*a+5)=some (x,b,m) ∧
    digitCode x b=some (aa,c) ∧ dd=m+3*b+c := by
  have hz : a≠0 := by omega
  have hnotleft : ¬ (d%2=1 ∧ a≥d+5) := by omega
  have hnoteven : ¬ (d%2=0 ∧ a≥d+3) := by omega
  have hnotpar : a%2≠1 := by omega
  have hnotdiag : a≠d+2 := by omega
  have hnotodd : d%2≠1 := by omega
  have hraw : (evalA (d+1-a) a (2*a+5)).bind
    (fun p => drainB p.1 p.2.1 p.2.2) = some (.D aa dd) := by
    simpa only [highLevelNext,if_neg hz,if_neg hnotleft,if_neg hnoteven,
      if_neg hnotpar,if_neg hnotdiag,if_neg hnotodd] using h
  cases he : evalA (d+1-a) a (2*a+5) with
  | none => simp [he] at hraw
  | some p =>
    rcases p with ⟨x,b,m⟩
    simp only [he,Option.bind_some] at hraw
    obtain ⟨c,hc,hdd⟩ := drainB_charge_witness x b m aa dd hraw
    exact ⟨x,b,m,c,rfl,hc,hdd⟩

#print axioms right_even_last_charge

#print axioms left_odd_mass
#print axioms left_even_mass
#print axioms right_odd_mass
#print axioms diagonal_mass

#print axioms left_odd_charge
#print axioms left_even_charge
#print axioms right_odd_charge
#print axioms diagonal_charge
end BB6.Agent8RootDigitChargeSource
