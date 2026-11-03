import GateNecessary
import BusyBeaver.BB6.M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA

namespace Agent10Original746
open CascadeSource CascadeSweep CascadeFatalExclusion
open BusyBeaver.M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA

private def toPair : HighLevelState → Nat × Nat
  | .C a b => (a,b)

/-- The actual upstream highLevelNext, not a copied transition, is definitionally
    identical to the compressed C-step model for all natural inputs. -/
theorem exact_high_level_step (a b : Nat) :
    (highLevelNext (.C a b)).map toPair = Cstep a b := by
  rcases b with _|_|d
  · rfl
  · rfl
  · by_cases hd : 2*a ≤ d
    · simp [highLevelNext, Cstep, hd, toPair]
    · by_cases hp : d%2=1
      · have hne : d%2≠0 := by omega
        simp [highLevelNext, Cstep, hd, hp, hne, toPair]
      · have he : d%2=0 := by omega
        simp [highLevelNext, Cstep, hd, hp, he, toPair]

/-- The upstream high-level next function, iterated from its actual post-initial
    state C(2,0), is reflected into our proved rooted C-episode relation. -/
def run : Nat → Option HighLevelState
  | 0 => some (.C 2 0)
  | n+1 => (run n).bind highLevelNext

theorem run_reaches (k a b : Nat)
    (h : run k = some (.C a b)) : ReachC (2,0) (a,b) := by
  induction k generalizing a b with
  | zero =>
    simp [run] at h
    rcases h with ⟨rfl,rfl⟩
    exact ReachC.refl _
  | succ k ih =>
    cases hr : run k with
    | none => simp [run,hr] at h
    | some s =>
      rcases s with ⟨u,v⟩
      have hr0 : ReachC (2,0) (u,v) := ih u v hr
      have he : highLevelNext (.C u v) = some (.C a b) := by
        simpa [run,hr] using h
      have hf := exact_high_level_step u v
      have he' : Cstep u v = some (a,b) := by
        simpa [he,toPair] using hf.symm
      exact ReachC.push hr0 he'

/-- Authentic source-connected, all-time exclusion of four fatal-height
    residue classes from the original high-level machine accelerated orbit. -/
theorem upstream_no_fatal_post_initial (n k : Nat)
    (hn : 6≤n) (hc : n%6=0∨n%6=1∨n%6=2∨n%6=3) :
    run k ≠ some (.C (4*2^n-n-4) 0) := by
  intro h
  exact no_fatal_root n hn hc (run_reaches k _ _ h)

/-- The original Cryptids high-level initial state takes one genuine step to
    the post-initial root (2,0); the full run is traced from its true start. -/
def startRun : Nat → Option HighLevelState
  | 0 => some highLevelStart
  | k+1 => (startRun k).bind highLevelNext

theorem startRun_successor (k : Nat) : startRun (k+1)=run k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (startRun (k+1)).bind highLevelNext = (run k).bind highLevelNext
    rw [ih]

/-- Original upstream acceleration from its exact initial state excludes every
    fatal index in the four full modulo-six residue classes, including n<6. -/
theorem upstream_no_fatal_from_true_start (n k : Nat)
    (hc : n%6=0∨n%6=1∨n%6=2∨n%6=3) :
    startRun k ≠ some (.C (4*2^n-n-4) 0) := by
  cases k with
  | zero => simp [startRun, highLevelStart]
  | succ k =>
    rw [startRun_successor]
    intro h
    exact CascadeSmallFatal.all_four_class_indices n hc (run_reaches k _ _ h)

/-- The first six excluded fatal indices of the true original acceleration. -/
theorem upstream_no_fatal_small_start (n k : Nat) (hn : n<6) :
    startRun k ≠ some (.C (4*2^n-n-4) 0) := by
  cases k with
  | zero => simp [startRun, highLevelStart]
  | succ k =>
    rw [startRun_successor]
    intro h
    exact CascadeSmallFatal.no_small_index n hn (run_reaches k _ _ h)

#print axioms upstream_no_fatal_from_true_start
#print axioms upstream_no_fatal_small_start

#print axioms upstream_no_fatal_post_initial
#print axioms exact_high_level_step
end Agent10Original746
