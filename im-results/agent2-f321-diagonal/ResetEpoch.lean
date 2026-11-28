import DiagonalCoordinates
import F321BackwardBarrier
import Lean.Elab.Tactic.Omega

/-!
Reset-to-reset epoch skeleton for the exact F321 counter map.

Between consecutive Middle resets, only High/Far/Equal non-Middle moves occur.  The
diagonal coordinate X=a+d+5 strictly increases on every such outer move, and
the next Middle reset's first counter 4a+6 lies strictly above the pre-reset X.
Consequently the first counter of every reset-to-reset epoch is strictly
increasing.  This supplies a well-founded global coordinate for future maximal
epoch decompositions.
-/

namespace BB6.Agent2F321ResetEpoch
open BB6.Agent31F321Density
open BB6.Agent2F321Diagonal

/-- Exactly one non-Middle live source move, written without branch ambiguity:
    High, Far, or Equal. -/
def OuterMove (a d A D : Nat) : Prop :=
  (d+2 ≤ a ∧ A=a-d-2 ∧ D=2*d+3) ∨
  (a<d ∧ 3*a+1≤d ∧ A=4*a+6 ∧ D=d-3*a) ∨
  (a=d ∧ A=2*a+4 ∧ D=1)

/-- Arbitrary finite High/Far/Equal interleaving. -/
inductive OuterRun : Nat → Nat → Nat → Nat → Nat → Prop
  | nil (a d) : OuterRun 0 a d a d
  | step {n a d A D B C} :
      OuterRun n a d A D → OuterMove A D B C →
      OuterRun (n+1) a d B C

/-- Exactly one Middle reset, including its parity-selected output counter. -/
def ResetMove (a d R c : Nat) : Prop :=
  (a<d ∧ d<3*a+1 ∧ (d-a)%2=0 ∧ R=4*a+6 ∧ c=2) ∨
  (a<d ∧ d<3*a+1 ∧ (d-a)%2=1 ∧ R=4*a+6 ∧ c=1)

/-- A reset epoch: a High/Far segment followed by the next Middle reset. -/
def ResetEpoch (R c R' c' : Nat) : Prop :=
  ∃ n a d, OuterRun n R c a d ∧ ResetMove a d R' c'

/-- Every exact live source move is either a non-Middle move or a Middle reset. -/
theorem move_outer_or_reset {a d A D : Nat}
    (h : CounterMove a d A D) :
    OuterMove a d A D ∨ ResetMove a d A D := by
  cases h with
  | high a d hg =>
      left
      unfold OuterMove
      exact Or.inl ⟨hg,rfl,rfl⟩
  | equal a =>
      left
      unfold OuterMove
      exact Or.inr (Or.inr ⟨rfl,rfl,rfl⟩)
  | far a d h1 h2 =>
      left
      unfold OuterMove
      exact Or.inr (Or.inl ⟨h1,h2,rfl,rfl⟩)
  | middleEven a d h1 h2 hp =>
      right
      unfold ResetMove
      exact Or.inl ⟨h1,h2,hp,rfl,rfl⟩
  | middleOdd a d h1 h2 hp =>
      right
      unfold ResetMove
      exact Or.inr ⟨h1,h2,hp,rfl,rfl⟩

/-- The two classes are guard-disjoint. -/
theorem outerMove_not_reset {a d A D : Nat}
    (ho : OuterMove a d A D) (hr : ResetMove a d A D) : False := by
  unfold OuterMove at ho
  unfold ResetMove at hr
  rcases hr with hr | hr
  · rcases hr with ⟨hr1,hr2,hp,rfl,rfl⟩
    rcases ho with ho | ho
    · rcases ho with ⟨hg,ha,hd⟩
      omega
    · rcases ho with hf | he
      · rcases hf with ⟨hf1,hf2,ha,hd⟩
        omega
      · rcases he with ⟨heq,ha,hd⟩
        omega
  · rcases hr with ⟨hr1,hr2,hp,rfl,rfl⟩
    rcases ho with ho | ho
    · rcases ho with ⟨hg,ha,hd⟩
      omega
    · rcases ho with hf | he
      · rcases hf with ⟨hf1,hf2,ha,hd⟩
        omega
      · rcases he with ⟨heq,ha,hd⟩
        omega

theorem outerMove_source {a d A D : Nat}
    (h : OuterMove a d A D) : CounterMove a d A D := by
  unfold OuterMove at h
  rcases h with hH | hRest
  · rcases hH with ⟨hg,rfl,rfl⟩
    exact CounterMove.high d hg
  · rcases hRest with hF | hE
    · rcases hF with ⟨h1,h2,rfl,rfl⟩
      exact CounterMove.far d h1 h2
    · rcases hE with ⟨rfl,rfl,rfl⟩
      exact CounterMove.equal a

theorem resetMove_source {a d R c : Nat}
    (h : ResetMove a d R c) : CounterMove a d R c := by
  unfold ResetMove at h
  rcases h with h | h
  · rcases h with ⟨h1,h2,hp,rfl,rfl⟩
    exact CounterMove.middleEven d h1 h2 hp
  · rcases h with ⟨h1,h2,hp,rfl,rfl⟩
    exact CounterMove.middleOdd d h1 h2 hp

/-- X strictly increases on every non-Middle move: +1 High, +6 Far, +5 Equal. -/
theorem outerMove_X_strict {a d A D : Nat}
    (h : OuterMove a d A D) : X a d < X A D := by
  unfold OuterMove at h
  rcases h with hH | hRest
  · rcases hH with ⟨hg,rfl,rfl⟩
    have hx := (high_coordinates a d hg).1
    omega
  · rcases hRest with hF | hE
    · rcases hF with ⟨h1,h2,rfl,rfl⟩
      have hx := (far_coordinates a d h1 h2).1
      omega
    · rcases hE with ⟨rfl,rfl,rfl⟩
      have hx := (equal_coordinates a).1
      omega

theorem outerMove_X_le_six {a d A D : Nat}
    (h : OuterMove a d A D) : X A D ≤ X a d + 6 := by
  unfold OuterMove at h
  rcases h with hH | hRest
  · rcases hH with ⟨hg,rfl,rfl⟩
    have hx := (high_coordinates a d hg).1
    omega
  · rcases hRest with hF | hE
    · rcases hF with ⟨h1,h2,rfl,rfl⟩
      have hx := (far_coordinates a d h1 h2).1
      omega
    · rcases hE with ⟨rfl,rfl,rfl⟩
      have hx := (equal_coordinates a).1
      omega

/-- Every non-Middle step raises X by at least one. -/
theorem outerRun_X_growth {n a d A D : Nat}
    (h : OuterRun n a d A D) :
    X a d + n ≤ X A D := by
  induction h with
  | nil => omega
  | step h hm ih =>
      have hs := outerMove_X_strict hm
      omega

theorem outerRun_X_upper {n a d A D : Nat}
    (h : OuterRun n a d A D) :
    X A D ≤ X a d + 6*n := by
  induction h with
  | nil => omega
  | step h hm ih =>
      have hs := outerMove_X_le_six hm
      omega

theorem outerRun_X_monotone {n a d A D : Nat}
    (h : OuterRun n a d A D) : X a d ≤ X A D := by
  induction h with
  | nil => exact Nat.le_refl _
  | step h hm ih =>
      have hs := outerMove_X_strict hm
      omega

/-- The next reset first counter lies strictly above the coordinate immediately
    before the reset. -/
theorem resetMove_output_bounds {a d R c : Nat}
    (h : ResetMove a d R c) :
    X a d < R ∧ R < 2 * X a d := by
  unfold ResetMove at h
  rcases h with h | h
  · rcases h with ⟨h1,h2,hp,rfl,rfl⟩
    unfold X
    omega
  · rcases h with ⟨h1,h2,hp,rfl,rfl⟩
    unfold X
    omega

theorem resetMove_output_above_X {a d R c : Nat}
    (h : ResetMove a d R c) : X a d < R :=
  (resetMove_output_bounds h).1

/-- Explicit two-sided distortion bound for an epoch with n non-Middle moves. -/
theorem resetEpoch_witness_bounds
    {n R c a d R' c' : Nat}
    (ho : OuterRun n R c a d)
    (hr : ResetMove a d R' c') :
    X R c + n < R' ∧
    R' < 2 * (X R c + 6*n) := by
  have hlo := outerRun_X_growth ho
  have hhi := outerRun_X_upper ho
  have hb := resetMove_output_bounds hr
  omega

/-- Stronger form: the next reset first counter lies above the entire starting
    reset coordinate, not merely above its first counter. -/
theorem resetEpoch_Xgap {R c R' c' : Nat}
    (h : ResetEpoch R c R' c') : X R c < R' := by
  rcases h with ⟨n,a,d,ho,hr⟩
  have h1 := outerRun_X_monotone ho
  have h2 := resetMove_output_above_X hr
  omega

theorem resetMove_output_small {a d R c : Nat}
    (h : ResetMove a d R c) : c = 1 ∨ c = 2 := by
  unfold ResetMove at h
  rcases h with h | h
  · rcases h with ⟨_,_,_,_,rfl⟩
    exact Or.inr rfl
  · rcases h with ⟨_,_,_,_,rfl⟩
    exact Or.inl rfl

/-- Any epoch beginning at a genuine reset counter c=1 or c=2 gains at least
    seven in its reset first counter. -/
theorem resetEpoch_gain7 {R c R' c' : Nat}
    (h : ResetEpoch R c R' c') (hc : 1 ≤ c) :
    R + 7 ≤ R' := by
  have hg := resetEpoch_Xgap h
  unfold X at hg
  omega

/-- Reset first counters are strictly increasing from one reset epoch to the
    next, independent of the High/Far/Equal interleaving length and branch pattern. -/
theorem resetEpoch_strict {R c R' c' : Nat}
    (h : ResetEpoch R c R' c') : R < R' := by
  rcases h with ⟨n,a,d,ho,hr⟩
  have h0 : R < X R c := by
    unfold X
    omega
  have h1 := outerRun_X_monotone ho
  have h2 := resetMove_output_above_X hr
  omega

/-- Every outer epoch is an exact canonical source-counter run. -/
theorem outerRun_counterReach {n a d A D : Nat}
    (h : OuterRun n a d A D) : CounterReach a d n A D := by
  induction h with
  | nil => exact CounterReach.nil
  | step h hm ih =>
      exact CounterReach.step ih (outerMove_source hm)

/-- Every reset epoch is an exact source run of one more step.  Its first
    counter increase also dominates the number of intervening non-Middle steps. -/
theorem resetEpoch_counterReach {R c R' c' : Nat}
    (h : ResetEpoch R c R' c') :
    ∃ n, CounterReach R c (n+1) R' c' ∧
      R + c + 6 + n ≤ R' := by
  rcases h with ⟨n,a,d,ho,hr⟩
  have hx := outerRun_X_growth ho
  have hreset := resetMove_output_above_X hr
  refine ⟨n, CounterReach.step (outerRun_counterReach ho) (resetMove_source hr), ?_⟩
  unfold X at hx hreset
  omega

theorem counterReach_append
    {sa sd n a d m A D : Nat}
    (h1 : CounterReach sa sd n a d)
    (h2 : CounterReach a d m A D) :
    CounterReach sa sd (n+m) A D := by
  induction h2 with
  | nil => simpa using h1
  | step hr hm ih =>
      have hs := CounterReach.step ih hm
      simpa [Nat.add_assoc] using hs

/-- Finite chains of reset epochs. -/
inductive ResetChain : Nat → Nat → Nat → Nat → Nat → Prop
  | nil (R c) : ResetChain 0 R c R c
  | step {n R c A e B f} :
      ResetChain n R c A e → ResetEpoch A e B f →
      ResetChain (n+1) R c B f

/-- Every reset chain denotes a genuine finite run of the canonical source map. -/
theorem resetChain_counterReach {n R c A e : Nat}
    (h : ResetChain n R c A e) :
    ∃ steps, CounterReach R c steps A e := by
  induction h with
  | nil => exact ⟨0, CounterReach.nil⟩
  | step hc he ih =>
      rcases ih with ⟨s,hs⟩
      rcases resetEpoch_counterReach he with ⟨m,hm,hgap⟩
      exact ⟨s+(m+1), counterReach_append hs hm⟩

theorem seed_only_equal {A D : Nat}
    (h : CounterMove 1 1 A D) : A = 6 ∧ D = 1 := by
  cases h <;> omega

/-- Strip the unique seed equal-move from every positive-time authentic run. -/
theorem root_tail_from_six_one {n A D : Nat}
    (h : CounterReach 1 1 (n+1) A D) :
    CounterReach 6 1 n A D := by
  induction n generalizing A D with
  | zero =>
      cases h with
      | step hr hm =>
          cases hr
          rcases seed_only_equal hm with ⟨rfl,rfl⟩
          exact CounterReach.nil
  | succ n ih =>
      cases h with
      | step hr hm =>
          have ht := ih hr
          exact CounterReach.step ht hm

/-- Canonical reset skeleton: completed reset epochs followed by one
    non-Middle suffix. -/
def ResetDecomposition (R c A D : Nat) : Prop :=
  ∃ q R0 c0 m,
    ResetChain q R c R0 c0 ∧ OuterRun m R0 c0 A D

/-- Every exact finite source run from a reset anchor has a reset decomposition. -/
theorem counterReach_reset_decomposition
    {R c n A D : Nat}
    (h : CounterReach R c n A D) :
    ResetDecomposition R c A D := by
  induction h with
  | nil =>
      exact ⟨0,R,c,0,ResetChain.nil R c,OuterRun.nil R c⟩
  | @step n a d A D h hm ih =>
      rcases ih with ⟨q,R0,c0,m,hchain,houter⟩
      rcases move_outer_or_reset hm with hout | hreset
      · exact ⟨q,R0,c0,m+1,hchain,OuterRun.step houter hout⟩
      · refine ⟨q+1,A,D,0,?_,OuterRun.nil A D⟩
        exact ResetChain.step hchain ⟨m,a,d,houter,hreset⟩

/-- Every positive-time authentic root state admits the canonical reset
    decomposition anchored at the first reset state (6,1). -/
theorem root_positive_reset_decomposition
    {n A D : Nat}
    (h : CounterReach 1 1 (n+1) A D) :
    ResetDecomposition 6 1 A D :=
  counterReach_reset_decomposition (root_tail_from_six_one h)

/-- The authentic root decomposition carries an explicit global lower bound on X
    in terms of the number of completed Middle-reset epochs. -/
theorem root_reset_count_X_bound
    {n A D : Nat}
    (h : CounterReach 1 1 (n+1) A D) :
    ∃ q R0 c0 m,
      ResetChain q 6 1 R0 c0 ∧
      OuterRun m R0 c0 A D ∧
      6 + 7*q < X A D := by
  rcases root_positive_reset_decomposition h with
    ⟨q,R0,c0,m,hchain,houter⟩
  refine ⟨q,R0,c0,m,hchain,houter,?_⟩
  exact decomposition_linear_X (by decide) hchain houter

/-- Quantitative consequence of the canonical decomposition: after q completed
    reset epochs, the current diagonal coordinate lies beyond R+7q. -/
theorem decomposition_linear_X
    {R c A D q R0 c0 m : Nat}
    (hc : 1 ≤ c)
    (hchain : ResetChain q R c R0 c0)
    (houter : OuterRun m R0 c0 A D) :
    R + 7*q < X A D := by
  have hg := resetChain_linear_growth hchain hc
  have hx := outerRun_X_monotone houter
  have hbase : R0 < X R0 c0 := by
    unfold X
    omega
  omega

theorem resetChain_end_positive {n R c A e : Nat}
    (h : ResetChain n R c A e) (hc : 1 ≤ c) : 1 ≤ e := by
  induction h with
  | nil => exact hc
  | step h he ih =>
      rcases he with ⟨m,a,d,ho,hr⟩
      have hs := resetMove_output_small hr
      omega

/-- A chain of n genuine reset epochs gains at least 7n in first counter. -/
theorem resetChain_linear_growth {n R c A e : Nat}
    (h : ResetChain n R c A e) (hc : 1 ≤ c) :
    R + 7*n ≤ A := by
  induction h with
  | nil => omega
  | @step n R c A e B f h he ih =>
      have hih := ih hc
      have hepos := resetChain_end_positive h hc
      have hg := resetEpoch_gain7 he hepos
      omega

theorem resetChain_monotone {n R c A e : Nat}
    (h : ResetChain n R c A e) : R ≤ A := by
  induction h with
  | nil => exact Nat.le_refl _
  | step hc he ih =>
      have hs := resetEpoch_strict he
      omega

theorem resetChain_strict {n R c A e : Nat}
    (h : ResetChain (n+1) R c A e) : R < A := by
  cases h with
  | step hc he =>
      have hm := resetChain_monotone hc
      have hs := resetEpoch_strict he
      omega

/-- In particular the exact reset-epoch skeleton has no positive cycle. -/
theorem no_reset_cycle {n R c e : Nat}
    (h : ResetChain (n+1) R c R e) : False := by
  have hs := resetChain_strict h
  omega

#print axioms outerRun_counterReach
#print axioms resetEpoch_counterReach
#print axioms resetChain_strict
#print axioms no_reset_cycle

#print axioms outerMove_source
#print axioms resetMove_source
#print axioms resetEpoch_strict
end BB6.Agent2F321ResetEpoch
