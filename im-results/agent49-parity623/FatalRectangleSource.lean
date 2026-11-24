import Agent49FlatDrainSource
import Agent49FatalCylinder

/-! No rectangular-periodic section invariant for the original #623 machine.
The two arithmetic namespaces below respectively establish cofinality and
fatal points in all independent arithmetic progressions. -/
namespace BB6.Agent49SectionCofinality
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

theorem evalA_bounds (a : Nat) : ∀ k m aa bb dd,
    evalA a k m = some (aa,bb,dd) → a+bb ≤ aa+k+1 ∧ m≤dd := by
  induction a with
  | zero =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases hk2 : k%3=2
    · simp [hk2] at h; cases h; omega
    · by_cases hk0 : k%3=0
      · simp [hk2,hk0] at h
      · simp [hk2,hk0] at h; cases h; omega
  | succ a ih =>
    intro k m aa bb dd h
    rw [evalA] at h
    by_cases hk2 : k%3=2
    · simp [hk2] at h; cases h; omega
    · by_cases hk0 : k%3=0
      · simp [hk2,hk0] at h; cases h; omega
      · simp [hk2,hk0] at h
        have hh := ih (k/3) (m+2*(k/3)+3) aa bb dd h
        omega

theorem drainB_bounds (b : Nat) : ∀ a d aa dd,
    drainB a b d = some (.D aa dd) → a≤aa+b ∧ d+2*b≤dd := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a d aa dd h
    rw [drainB] at h
    by_cases hz : b=0
    · simp [hz] at h; cases h; omega
    · simp only [if_neg hz] at h
      cases he : evalA a (b-1) (d+2*b+3) with
      | none => simp [he] at h
      | some p =>
        rcases p with ⟨a1,b1,d1⟩
        simp only [he,Option.bind_some] at h
        by_cases hlt : b1<b
        · simp only [if_pos hlt] at h
          have h1 := evalA_bounds a (b-1) (d+2*b+3) a1 b1 d1 he
          have h2 := ih b1 hlt a1 d1 aa dd h
          omega
        · simp [hlt] at h

/-- If the total is large but one counter is small, any successful return
strictly increases the smaller counter. This includes the a=0 branches. -/
theorem small_min_increases (K a d aa dd : Nat)
    (hmass : 4*K+10≤a+d) (hmin : min a d≤K)
    (hstep : highLevelNext (.D a d) = some (.D aa dd)) :
    min a d < min aa dd := by
  simp only [highLevelNext] at hstep
  by_cases hz : a=0
  · simp only [if_pos hz] at hstep
    by_cases hd : d%2=1
    · simp only [if_pos hd] at hstep
      have hh := drainB_bounds 2 (d+1) 2 aa dd hstep
      omega
    · simp only [if_neg hd] at hstep; cases hstep; omega
  · simp only [if_neg hz] at hstep
    by_cases h1 : d%2=1 ∧ a≥d+5
    · simp only [if_pos h1] at hstep
      have hh := drainB_bounds (d+3) (a-d-5) 5 aa dd hstep
      omega
    · simp only [if_neg h1] at hstep
      by_cases h2 : d%2=0 ∧ a≥d+3
      · simp only [if_pos h2] at hstep
        have hh := drainB_bounds (d+2) (a-d-2) 2 aa dd hstep
        omega
      · simp only [if_neg h2] at hstep
        by_cases h3 : a%2=1
        · simp [h3] at hstep
        · simp only [if_neg h3] at hstep
          by_cases h4 : a=d+2
          · omega
          · simp only [if_neg h4] at hstep
            by_cases h5 : d%2=1
            · simp only [if_pos h5] at hstep
              have hh := drainB_bounds (a-1) (d+4-a) 3 aa dd hstep
              omega
            · simp only [if_neg h5] at hstep
              cases he : evalA (d+1-a) a (2*a+5) with
              | none => simp [he] at hstep
              | some p =>
                rcases p with ⟨a1,b1,d1⟩
                simp only [he,Option.bind_some] at hstep
                have hA := evalA_bounds (d+1-a) a (2*a+5) a1 b1 d1 he
                have hB := drainB_bounds b1 a1 d1 aa dd hstep
                omega

/-- Every infinite successful high-level trajectory whose mass tends to
infinity has a section visit with both counters greater than K. -/
theorem trajectory_cofinal (a d : Nat → Nat)
    (hstep : ∀ n, highLevelNext (.D (a n) (d n)) = some (.D (a (n+1)) (d (n+1))))
    (hmass : ∀ K, ∃ N, ∀ n, N≤n → K≤a n+d n) :
    ∀ K, ∃ n, K<a n ∧ K<d n := by
  intro K
  by_cases hgood : ∃ n, K<a n ∧ K<d n
  · exact hgood
  exfalso
  have hbad (n : Nat) : min (a n) (d n)≤K := by
    by_cases ha : K<a n
    · by_cases hd : K<d n
      · exact False.elim (hgood ⟨n,ha,hd⟩)
      · omega
    · omega
  obtain ⟨N,hN⟩ := hmass (4*K+10)
  have hinc (n : Nat) (hn : N≤n) : min (a n) (d n) < min (a (n+1)) (d (n+1)) :=
    small_min_increases K _ _ _ _ (hN n hn) (hbad n) (hstep n)
  have hl (t : Nat) : t≤min (a (N+t)) (d (N+t)) := by
    induction t with
    | zero => omega
    | succ t ih =>
      have hh := hinc (N+t) (by omega)
      rw [Nat.add_assoc] at hh
      omega
  have hx := hl (K+1)
  have hb := hbad (N+(K+1))
  omega

#print axioms small_min_increases
#print axioms trajectory_cofinal
end BB6.Agent49SectionCofinality

namespace BB6.Agent49FatalRectangleSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49FlatDrainSource BB6.Agent49FatalCylinder BB6.Agent49ParitySource

def Fatal (a b : Nat) : Prop := ∀ d, drainB a b d=none

theorem drainRules : Rules Fatal where
  zero := drain_three_one_zero
  lift0 := by
    intro a b h d
    rw [drain_three a (b+1) d (by omega)]
    simpa using h (d+6*(b+1)+3)
  lift1 := by
    intro a b h d
    rw [drain_three_one (a+1) b d (by omega)]
    simpa using h (d+6*b+7)
  lift2 := by
    intro a b hb h d
    rw [drain_three_two (a+1) (b-1) d (by omega)]
    have hq : b-1+1=b := by omega
    rw [hq]
    simpa using h (d+6*(b-1)+5)

theorem gap_choice (p a0 d0 delta : Nat) (hp : 0<p) :
    ∃ A i, p≤A ∧ d0+delta+A=a0+p*i := by
  let i := d0+delta+1
  let A := a0+p*i-(d0+delta)
  have h := Nat.mul_le_mul_right (d0+delta) (show 1≤p by omega)
  simp only [Nat.one_mul] at h
  have hi : p*i=p*(d0+delta)+p := by simp [i,Nat.mul_add]
  exact ⟨A,i,by dsimp [A]; omega,by dsimp [A]; omega⟩

/-- Every upper-right rectangle of independent arithmetic progressions
with a common positive even period contains a one-return halter. -/
theorem fatal_rectangle (P a0 d0 : Nat) (hP : 0<P) :
    ∃ i j, highLevelNext (.D (a0+2*P*i) (d0+2*P*j))=none := by
  let p := 2*P
  have hp : 0<p := by dsimp [p]; omega
  have hp2 : 2≤p := by dsimp [p]; omega
  let delta := if d0%2=1 then 5 else 2
  let c := if d0%2=1 then 3 else 2
  obtain ⟨A,i,hA,hi⟩ := gap_choice p a0 d0 delta hp
  obtain ⟨j,hj⟩ := fatal_progression drainRules p A (d0+c) hp hA
  let d := d0+p*j
  let a := a0+p*(i+j)
  have ha : a=d+delta+A := by
    dsimp [a,d]
    rw [Nat.mul_add]
    omega
  have hpar : d%2=d0%2 := by
    dsimp [d,p]
    rw [Nat.mul_assoc]
    omega
  have hb : d0+c+p*j=d+c := by dsimp [d]; omega
  rw [hb] at hj
  refine ⟨i+j,j,?_⟩
  change highLevelNext (.D a d)=none
  have ha0 : a≠0 := by omega
  by_cases hodd : d0%2=1
  · have hd : d%2=1 := by omega
    have hdel : delta=5 := by simp [delta,hodd]
    have hc : c=3 := by simp [c,hodd]
    have hcond : d%2=1 ∧ a≥d+5 := ⟨hd,by omega⟩
    have hgap : a-d-5=A := by omega
    simp only [highLevelNext,if_neg ha0,if_pos hcond,hgap]
    rw [hc] at hj
    exact hj 5
  · have hd : d%2=0 := by omega
    have hdel : delta=2 := by simp [delta,hodd]
    have hc : c=2 := by simp [c,hodd]
    have hcond : ¬(d%2=1 ∧ a≥d+5) := by omega
    have hcond2 : d%2=0 ∧ a≥d+3 := ⟨hd,by omega⟩
    have hgap : a-d-2=A := by omega
    simp only [highLevelNext,if_neg ha0,if_neg hcond,if_pos hcond2,hgap]
    rw [hc] at hj
    exact hj 2

/-- A predicate stable under separate period shifts above N cannot be both
safe for every section and contain any section above N in both counters. -/
theorem no_periodic_safe_cell (Q : Nat → Nat → Prop) (P N : Nat) (hP : 0<P)
    (hper : ∀ a d i j, N≤a → N≤d → Q a d → Q (a+2*P*i) (d+2*P*j))
    (hsafe : ∀ a d, Q a d → highLevelNext (.D a d)≠none) :
    ∀ a d, N≤a → N≤d → ¬ Q a d := by
  intro a d ha hd hQ
  obtain ⟨i,j,hhalt⟩ := fatal_rectangle P a d hP
  exact hsafe _ _ (hper a d i j ha hd hQ) hhalt

/-- No eventually rectangular-periodic safe predicate contains an infinite
successful trajectory of unbounded mass. -/
theorem no_periodic_trajectory (Q : Nat → Nat → Prop) (P N : Nat) (hP : 0<P)
    (hper : ∀ a d i j, N≤a → N≤d → Q a d → Q (a+2*P*i) (d+2*P*j))
    (hsafe : ∀ a d, Q a d → highLevelNext (.D a d)≠none)
    (a d : Nat → Nat)
    (hstep : ∀ n, highLevelNext (.D (a n) (d n)) = some (.D (a (n+1)) (d (n+1))))
    (hmass : ∀ K, ∃ M, ∀ n, M≤n → K≤a n+d n)
    (hQ : ∀ n, Q (a n) (d n)) : False := by
  obtain ⟨n,ha,hd⟩ := BB6.Agent49SectionCofinality.trajectory_cofinal a d hstep hmass N
  exact no_periodic_safe_cell Q P N hP hper hsafe (a n) (d n) (by omega) (by omega) (hQ n)

/-- A safe inductive predicate containing the blank-origin section cannot
have independent eventual arithmetic periodicity in both counters. -/
theorem no_periodic_root_invariant (Q : Nat → Nat → Prop) (P N : Nat)
    (hP : 0<P)
    (hper : ∀ a d i j, N≤a → N≤d → Q a d → Q (a+2*P*i) (d+2*P*j))
    (hclosed : ∀ a d, Q a d → ∃ aa dd,
        highLevelNext (.D a d)=some (.D aa dd) ∧ Q aa dd)
    (hroot : Q 0 7) : False := by
  have hr : ∀ n, ∃ a d, run n=some (.D a d) ∧ Q a d := by
    intro n
    induction n with
    | zero => exact ⟨0,7,rfl,hroot⟩
    | succ n ih =>
      obtain ⟨a,d,hrun,hQ⟩ := ih
      obtain ⟨aa,dd,hn,hQ'⟩ := hclosed a d hQ
      refine ⟨aa,dd,?_,hQ'⟩
      simp only [run,hrun,Option.bind_some]
      exact hn
  let a (n : Nat) := Classical.choose (hr n)
  let d (n : Nat) := Classical.choose (Classical.choose_spec (hr n))
  have hrun (n : Nat) : run n=some (.D (a n) (d n)) :=
    (Classical.choose_spec (Classical.choose_spec (hr n))).1
  have hQ (n : Nat) : Q (a n) (d n) :=
    (Classical.choose_spec (Classical.choose_spec (hr n))).2
  have hstep (n : Nat) : highLevelNext (.D (a n) (d n))=some (.D (a (n+1)) (d (n+1))) := by
    have hh := hrun (n+1)
    simp only [run,hrun n,Option.bind_some] at hh
    exact hh
  have hmass : ∀ K, ∃ M, ∀ n, M≤n → K≤a n+d n := by
    intro K
    refine ⟨K,?_⟩
    intro n hn
    have hh := run_grows_at_least_seven n _ _ (hrun n)
    omega
  have hsafe (a d : Nat) (hQ : Q a d) : highLevelNext (.D a d)≠none := by
    obtain ⟨aa,dd,h,_⟩ := hclosed a d hQ
    rw [h]
    simp
  exact no_periodic_trajectory Q P N hP hper hsafe a d hstep hmass hQ

#print axioms fatal_rectangle
#print axioms no_periodic_safe_cell
#print axioms no_periodic_trajectory
#print axioms no_periodic_root_invariant
end BB6.Agent49FatalRectangleSource
