import BusyBeaver.BB6.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

/-!
  Uniform translation of the *first* counter in the safe B-drain domain.
  This proof references the unchanged original DeepMind Cryptids accelerator.
  Original source revision: c86f15861709b76042998c5211c7b2f83991621b.
  Theorems are conditional on exact numerical bounds, not blank reachability.
-/

namespace BB6.Agent8FirstSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

def liftFirstEval (t : Nat) : Nat × Nat × Nat → Nat × Nat × Nat
  | (a,b,d) => (a+t,b,d)

def liftFirstState (t : Nat) : HighLevelState → HighLevelState
  | .D a d => .D (a+t) d

theorem evalA_first_shift (a : Nat) : ∀ k m t : Nat, k + 2 ≤ a →
  evalA (a+t) k m = (evalA a k m).map (liftFirstEval t) := by
  induction a with
  | zero =>
    intro k m t h
    omega
  | succ a ih =>
    intro k m t h
    have ht : (a+1)+t = (a+t)+1 := by omega
    rw [ht]
    conv => lhs; rw [evalA]
    conv => rhs; rw [evalA]
    by_cases h2 : k%3=2
    · simp only [if_pos h2, Option.map_some]
      simp [liftFirstEval, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · simp only [if_neg h2]
      have hpos1 : (a+t)+1 ≠ 0 := by omega
      have hpos2 : a+1 ≠ 0 := by omega
      simp only [if_neg hpos1, if_neg hpos2]
      by_cases h0 : k%3=0
      · simp only [if_pos h0, Option.map_some, liftFirstEval]
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · simp only [if_neg h0]
        have hsub1 : (a+t+1)-1 = a+t := by omega
        have hsub2 : (a+1)-1 = a := by omega
        rw [hsub1,hsub2]
        exact ih (k/3) (m+2*(k/3)+3) t (by omega)

theorem evalA_b_le_k (a : Nat) :
    ∀ k m aa bb dd : Nat, evalA a k m = some (aa,bb,dd) → bb ≤ k := by
  induction a with
  | zero =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases h2 : k%3 = 2
    · simp [h2] at h
      cases h
      omega
    · by_cases h0 : k%3 = 0
      · simp [h2,h0] at h
      · simp [h2,h0] at h
        cases h
        omega
  | succ a ih =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases h2 : k%3 = 2
    · simp [h2] at h
      cases h
      omega
    · by_cases h0 : k%3 = 0
      · simp [h2,h0] at h
        cases h
        omega
      · simp [h2,h0] at h
        have ht := ih (k/3) (m+2*(k/3)+3) aa bb dd h
        omega

theorem evalA_safe_gap (a : Nat) : ∀ k m : Nat, k + 2 ≤ a →
    ∃ aa bb dd, evalA a k m = some (aa,bb,dd) ∧ bb < aa := by
  induction a with
  | zero =>
    intro k m hk
    omega
  | succ a ih =>
    intro k m hk
    rw [evalA]
    by_cases h2 : k%3 = 2
    · simp only [if_pos h2]
      refine ⟨a+2,k/3,m,rfl,?_⟩
      omega
    · by_cases h0 : k%3 = 0
      · simp only [if_neg h2, Nat.succ_ne_zero, if_pos h0]
        refine ⟨a,k/3,m+2,rfl,?_⟩
        omega
      · have hgap : k/3+2 ≤ a := by omega
        obtain ⟨aa,bb,dd,he,hlt⟩ := ih (k/3) (m+2*(k/3)+3) hgap
        simp only [if_neg h2, Nat.succ_ne_zero, if_neg h0]
        exact ⟨aa,bb,dd,he,hlt⟩

theorem drainB_first_shift (b : Nat) : ∀ a d t : Nat, b < a →
    drainB (a+t) b d = (drainB a b d).map (liftFirstState t) := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a d t ha
    conv => lhs; rw [drainB]
    conv => rhs; rw [drainB]
    by_cases hb : b = 0
    · simp [hb,liftFirstState]
    · simp only [if_neg hb]
      have hgap : (b-1)+2 ≤ a := by omega
      obtain ⟨aa,bb,dd,he,hr⟩ := evalA_safe_gap a (b-1) (d+2*b+3) hgap
      have hbb : bb < b := by
        have hle := evalA_b_le_k a (b-1) (d+2*b+3) aa bb dd he
        omega
      have hshift := evalA_first_shift a (b-1) (d+2*b+3) t hgap
      rw [hshift,he]
      simp only [Option.map_some, liftFirstEval, Option.bind_some, if_pos hbb]
      exact ih bb hbb aa dd t hr

/-- Every far-left odd-d successor is a first-coordinate translate. -/
theorem highLevel_far_odd_shift (a d t : Nat)
    (hd : d % 2 = 1) (ha : 2*d+8 < a) :
    highLevelNext (.D (a+t) d) =
      (highLevelNext (.D a d)).map (liftFirstState t) := by
  conv => lhs; rw [highLevelNext]
  conv => rhs; rw [highLevelNext]
  have hz : a ≠ 0 := by omega
  have hzt : a+t ≠ 0 := by omega
  have hbase : d%2=1 ∧ a ≥ d+5 := ⟨hd,by omega⟩
  have hnew : d%2=1 ∧ a+t ≥ d+5 := ⟨hd,by omega⟩
  simp only [if_neg hz, if_neg hzt, if_pos hbase, if_pos hnew]
  have heq : a+t-d-5 = (a-d-5)+t := by omega
  rw [heq]
  exact drainB_first_shift (d+3) (a-d-5) 5 t (by omega)

/-- Every far-left even-d successor is a first-coordinate translate. -/
theorem highLevel_far_even_shift (a d t : Nat)
    (hd : d % 2 = 0) (ha : 2*d+4 < a) :
    highLevelNext (.D (a+t) d) =
      (highLevelNext (.D a d)).map (liftFirstState t) := by
  conv => lhs; rw [highLevelNext]
  conv => rhs; rw [highLevelNext]
  have hz : a ≠ 0 := by omega
  have hzt : a+t ≠ 0 := by omega
  have hnot0 : ¬ (d%2=1 ∧ a ≥ d+5) := by omega
  have hnotT : ¬ (d%2=1 ∧ a+t ≥ d+5) := by omega
  have hbase : d%2=0 ∧ a ≥ d+3 := ⟨hd,by omega⟩
  have hnew : d%2=0 ∧ a+t ≥ d+3 := ⟨hd,by omega⟩
  simp only [if_neg hz, if_neg hzt, if_neg hnot0, if_neg hnotT,
     if_pos hbase, if_pos hnew]
  have heq : a+t-d-2 = (a-d-2)+t := by omega
  rw [heq]
  exact drainB_first_shift (d+2) (a-d-2) 2 t (by omega)


/-- Far-right odd-d rays become first-counter translations after two-unit input shifts. -/
theorem highLevel_right_odd_shift (a d t : Nat)
    (ha : 0 < a) (hae : a%2=0) (hd : d%2=1) (hg : 2*a+1 ≤ d) :
    highLevelNext (.D a (d+2*t)) =
      (highLevelNext (.D a d)).map (liftFirstState (2*t)) := by
  conv => lhs; rw [highLevelNext]
  conv => rhs; rw [highLevelNext]
  have h0 : a ≠ 0 := by omega
  have h1 : ¬(d%2=1 ∧ a ≥ d+5) := by omega
  have h1t : ¬((d+2*t)%2=1 ∧ a ≥ (d+2*t)+5) := by omega
  have h2 : ¬(d%2=0 ∧ a ≥ d+3) := by omega
  have h2t : ¬((d+2*t)%2=0 ∧ a ≥ (d+2*t)+3) := by omega
  have hodd : a%2 ≠ 1 := by omega
  have heq : a ≠ d+2 := by omega
  have heqt : a ≠ (d+2*t)+2 := by omega
  have hdt : (d+2*t)%2=1 := by omega
  simp only [if_neg h0,if_neg h1,if_neg h1t,if_neg h2,if_neg h2t,
      if_neg hodd,if_neg heq,if_neg heqt,if_pos hd,if_pos hdt]
  have he : d+2*t+4-a = (d+4-a)+2*t := by omega
  rw [he]
  exact drainB_first_shift (a-1) (d+4-a) 3 (2*t) (by omega)

/-- Far-right even-d rays likewise become exact first-counter translations. -/
theorem highLevel_right_even_shift (a d t : Nat)
    (ha : 0 < a) (hae : a%2=0) (hd : d%2=0) (hg : 2*a+2 ≤ d) :
    highLevelNext (.D a (d+2*t)) =
      (highLevelNext (.D a d)).map (liftFirstState (2*t)) := by
  conv => lhs; rw [highLevelNext]
  conv => rhs; rw [highLevelNext]
  have h0 : a ≠ 0 := by omega
  have h1 : ¬(d%2=1 ∧ a ≥ d+5) := by omega
  have h1t : ¬((d+2*t)%2=1 ∧ a ≥ (d+2*t)+5) := by omega
  have h2 : ¬(d%2=0 ∧ a ≥ d+3) := by omega
  have h2t : ¬((d+2*t)%2=0 ∧ a ≥ (d+2*t)+3) := by omega
  have hodd : a%2 ≠ 1 := by omega
  have heq : a ≠ d+2 := by omega
  have heqt : a ≠ (d+2*t)+2 := by omega
  have hdodd : d%2 ≠ 1 := by omega
  have hdt : (d+2*t)%2 ≠ 1 := by omega
  simp only [if_neg h0,if_neg h1,if_neg h1t,if_neg h2,if_neg h2t,
      if_neg hodd,if_neg heq,if_neg heqt,if_neg hdodd,if_neg hdt]
  have hevalGap : a+2 ≤ d+1-a := by omega
  obtain ⟨aa,bb,dd,heval,hsafe⟩ := evalA_safe_gap (d+1-a) a (2*a+5) hevalGap
  have hes : d+2*t+1-a = (d+1-a)+2*t := by omega
  rw [hes,evalA_first_shift (d+1-a) a (2*a+5) (2*t) hevalGap,heval]
  simp only [Option.map_some,liftFirstEval,Option.bind_some]
  exact drainB_first_shift bb aa dd (2*t) hsafe

#print axioms highLevel_right_odd_shift
#print axioms highLevel_right_even_shift


/-- In the positive-gap cone, the evaluator preserves third-plus-residual parity. -/
theorem evalA_safe_d_parity (a : Nat) : ∀ k m aa bb dd : Nat,
    k+2 ≤ a → evalA a k m = some (aa,bb,dd) →
    (dd+bb)%2 = (m+k)%2 := by
  induction a with
  | zero =>
    intro k m aa bb dd hg h
    omega
  | succ a ih =>
    intro k m aa bb dd hg h
    rw [evalA] at h
    by_cases h2 : k%3=2
    · simp [h2] at h
      cases h
      omega
    · by_cases h0 : k%3=0
      · simp [h2,h0] at h
        cases h
        omega
      · simp [h2,h0] at h
        have hp := ih (k/3) (m+2*(k/3)+3) aa bb dd (by omega) h
        omega

/-- A successful B-drain with b<a shifts third-counter parity by exactly b. -/
theorem drainB_safe_d_parity (b : Nat) : ∀ a d aa dd : Nat,
    b < a → drainB a b d = some (.D aa dd) →
    dd%2 = (d+b)%2 := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a d aa dd hgap h
    rw [drainB] at h
    by_cases hb : b=0
    · simp [hb] at h
      cases h
      omega
    · simp only [if_neg hb] at h
      have hevalGap : (b-1)+2 ≤ a := by omega
      obtain ⟨a1,b1,d1,heval,hlt⟩ :=
        evalA_safe_gap a (b-1) (d+2*b+3) hevalGap
      have hdec : b1 < b := by
        have hle := evalA_b_le_k a (b-1) (d+2*b+3) a1 b1 d1 heval
        omega
      rw [heval] at h
      simp only [Option.bind_some, if_pos hdec] at h
      have hp := evalA_safe_d_parity a (b-1) (d+2*b+3)
          a1 b1 d1 hevalGap heval
      have hr := ih b1 hdec a1 d1 aa dd hlt h
      omega

#print axioms evalA_safe_d_parity
#print axioms drainB_safe_d_parity

#print axioms evalA_first_shift
#print axioms drainB_first_shift
#print axioms highLevel_far_odd_shift
#print axioms highLevel_far_even_shift
end BB6.Agent8FirstSource
