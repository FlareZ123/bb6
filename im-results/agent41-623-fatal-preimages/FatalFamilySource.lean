import Agent49InverseWindowSource
import FatalFamilyInfinite

/-! Root exclusion for the explicit near-power three-return halting family.
The original-machine transition, parity invariant, and complete parent
envelope are imported without alteration. -/
namespace BB6.Agent41FatalInverseSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49InverseWindowSource BB6.Agent49CorrectionGrowth BB6.Agent41FatalInverse

def ParameterGate (k : Nat) : Prop :=
  (∃ t, t≤k+2 ∧ LeftParameter k t) ∨ (∃ t, t≤k+1 ∧ RightParameter k t)

private def P (A b z x y : Nat) : Prop :=
  Window A b z x y ∧ (2*inverseBudget y≤x → y=z+image b)

private theorem P_sound (A b z x y : Nat) (h : drainB A b z=some (.D x y)) : P A b z x y :=
  ⟨source_drain_window A b z x y h, source_large_first_image A b z x y h⟩

/-- The necessary parameter disjunction for every even-first source parent. -/
theorem parent_parameter (k a d : Nat) (hk : 7≤k) (ho : k%2=1) (ha : a%2=0)
    (h : highLevelNext (.D a d)=some (.D (targetX k) (targetY k))) : ParameterGate k := by
  have hbig : 2*inverseBudget (targetY k)≤targetX k := large_first k hk
  have hsmall : inverseBudget (targetY k)≤2*(k+1)+3 := budget_le k hk
  have hn : 0 < inverseBudget (targetY k) := by unfold inverseBudget; omega
  have hy := targetY_even k hk ho
  have hgt := targetY_gt14 k hk
  have henv := parent_envelope_complete P P_sound _ _ _ _ h
  unfold ParentEnvelope at henv
  rcases henv with haxis|hLO|hLE|hdiag|hRO|hRE
  · rcases haxis.2 with h|h <;> omega
  · obtain ⟨A,b,hd,_,_,hb,hP⟩ := hLO
    have hi := hP.2 hbig
    have hp := image_parity b
    omega
  · obtain ⟨A,b,hd,_,_,hb,hP⟩ := hLE
    have hi := hP.2 hbig
    have hw := hP.1
    unfold Window at hw
    have he : excess b≤4*(2*(k+1)+3) := by unfold image at hi; omega
    exact Or.inl (left_parameter_necessary k b hk ho (by omega) hi he)
  · obtain ⟨_,_,hP⟩ := hdiag
    have hw := hP.1
    unfold Window at hw
    omega
  · obtain ⟨A,b,ha,hd,hb,_,hP⟩ := hRO
    have hi := hP.2 hbig
    have hw := hP.1
    unfold Window at hw
    have he : excess b≤4*(2*(k+1)+3) := by unfold image at hi; omega
    exact Or.inr (right_parameter_necessary k b hk ho (by omega) hi he)
  · obtain ⟨A,b,ha,hd,hb,_,hP⟩ := hRE
    have hi := hP.2 hbig
    have hp := image_parity b
    omega

/-- Every authentic blank-origin visit to the family forces the gate. -/
theorem root_parameter (k i : Nat) (hk : 7≤k) (ho : k%2=1)
    (h : BB6.Agent49ParitySource.run i = some (.D (targetX k) (targetY k))) : ParameterGate k := by
  cases i with
  | zero =>
    have hy := targetY_gt14 k hk
    simp only [BB6.Agent49ParitySource.run, Option.some.injEq, HighLevelState.D.injEq] at h
    omega
  | succ i =>
    simp only [BB6.Agent49ParitySource.run] at h
    cases he : BB6.Agent49ParitySource.run i with
    | none => simp [he] at h
    | some s =>
      rcases s with ⟨a,d⟩
      simp only [he,Option.bind_some] at h
      exact parent_parameter k a d hk ho (BB6.Agent49ParitySource.run_preserves_even i a d he) h

/-- No gate means exclusion at every blank-origin return index. -/
theorem root_excluded (k : Nat) (hk : 7≤k) (ho : k%2=1) (hgate : ¬ ParameterGate k) :
    ∀ i, BB6.Agent49ParitySource.run i ≠ some (.D (targetX k) (targetY k)) :=
  fun i h => hgate (root_parameter k i hk ho h)

/-- Every exponent p=6*3^r, r>=1, gives an authentic root exclusion at
all return indices, despite its synthetic three-return halt. -/
theorem power_three_root_excluded (r : Nat) (hr : 1≤r) :
    let k := 6*3^r-1
    ∀ i, BB6.Agent49ParitySource.run i ≠ some (.D (targetX k) (targetY k)) := by
  dsimp only
  let k := 6*3^r-1
  have hp : 3≤3^r := by
    obtain ⟨s,hs⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r≠0)
    rw [hs,Nat.pow_succ]
    have hpos : 0<3^s := Nat.pow_pos (by decide)
    omega
  have hk : 7≤k := by dsimp [k]; omega
  have ho : k%2=1 := by dsimp [k]; omega
  obtain ⟨hl,hh⟩ := power_three_gates_excluded r hr
  apply root_excluded k hk ho
  intro hg
  rcases hg with ⟨t,_,ht⟩|⟨t,_,ht⟩
  · exact hl t ht
  · exact hh t ht

#print axioms parent_parameter
#print axioms root_parameter
#print axioms root_excluded
#print axioms power_three_root_excluded
end BB6.Agent41FatalInverseSource
