import Mass
import SweepInvariant
import FatalExclusion

namespace CascadeSmallFatal
open CascadeSource CascadeSweep

/-- Exact C-episode trajectory, preserving halts as none. -/
def runC (x : Nat × Nat) : Nat → Option (Nat × Nat)
  | 0 => some x
  | k+1 => (runC x k).bind (fun z => Cstep z.1 z.2)

/-- Every C-episode reachability proof carries a finite exact step count. -/
theorem reach_has_count {x y : Nat × Nat} (h : ReachC x y) :
    ∃ k, runC x k=some y := by
  induction h with
  | refl => exact ⟨0,rfl⟩
  | push hstep h ih =>
    obtain ⟨k,heq⟩ := ih
    exact ⟨k+1,by simp [runC,heq,h]⟩

/-- After 28 exact episodes the true blank-root orbit has crossed mass 238;
    all future defined episodes have strictly larger mass. -/
theorem after_28_mass (k : Nat) (s : Nat×Nat)
    (h : runC (2,0) (28+k)=some s) :
    238 < 2*s.1+s.2 := by
  induction k generalizing s with
  | zero =>
    have hval : runC (2,0) 28=some (218,0) := by decide
    rw [hval] at h
    cases h
    decide
  | succ k ih =>
    cases heq : runC (2,0) (28+k) with
    | none => simp [runC,heq] at h
    | some z =>
      rcases z with ⟨a,b⟩
      have hm : 238<2*a+b := ih (a,b) heq
      have he' : Cstep a b=some s := by simpa [runC,heq] using h
      rcases s with ⟨u,v⟩
      have hs : 2*a+b<2*u+v := Cstep_mass_strict a b u v he'
      omega

/-- Finite exact decidable certificate for the six small candidate heights. -/
theorem prefix_avoids_six (t : Nat)
    (ht : t=0 ∨ t=3 ∨ t=10 ∨ t=25 ∨ t=56 ∨ t=119) :
    ∀ k : Fin 28, runC (2,0) k.1 ≠ some (t,0) := by
  rcases ht with h|h|h|h|h|h <;> subst t <;> decide

/-- The authentic post-initial C(2,0) orbit never hits the six fatal reset
    heights with n<6, including the complementary residues 4,5. -/
theorem no_small_fatal (t : Nat)
    (ht : t=0 ∨ t=3 ∨ t=10 ∨ t=25 ∨ t=56 ∨ t=119) :
    ¬ReachC (2,0) (t,0) := by
  intro h
  obtain ⟨k,hk⟩ := reach_has_count h
  by_cases hb : k<28
  · exact (prefix_avoids_six t ht ⟨k,hb⟩) hk
  · have hki : k=28+(k-28) := by omega
    rw [hki] at hk
    have hm := after_28_mass (k-28) (t,0) hk
    rcases ht with ht|ht|ht|ht|ht|ht <;> subst t <;> simp at hm

/-- All first six fatal index values, including n=4,5, are excluded. -/
theorem no_small_index (n : Nat) (hn : n<6) :
    ¬ReachC (2,0) (4*2^n-n-4,0) := by
  have hcases : n=0∨n=1∨n=2∨n=3∨n=4∨n=5 := by omega
  rcases hcases with h|h|h|h|h|h <;> subst n <;>
    exact no_small_fatal _ (by decide)

/-- Every index in four complete mod-six classes is excluded, including
    n=0,1,2,3, and additionally the first two complementary indices 4,5. -/
theorem all_four_class_indices (n : Nat)
    (hc : n%6=0 ∨ n%6=1 ∨ n%6=2 ∨ n%6=3) :
    ¬ReachC (2,0) (4*2^n-n-4,0) := by
  by_cases hs : n<6
  · exact no_small_index n hs
  · exact CascadeFatalExclusion.no_fatal_root n (by omega) hc

#print axioms no_small_index
#print axioms all_four_class_indices

#print axioms no_small_fatal
#print axioms prefix_avoids_six
end CascadeSmallFatal
