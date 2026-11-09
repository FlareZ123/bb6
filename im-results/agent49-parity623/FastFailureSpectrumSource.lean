import Agent49FullFailureSpectrumSource

/-!
A compact, exact list of every first-counter value that makes the original
Cryptids #623 drain fail for any fixed block count b.
Each recursive call reduces b to at most floor(b/2). The computed list has
length O(log b), and third-counter independence is inherited from the
source-authenticated full-range predicate. This is an intermediate theorem;
the authentic blank-root trajectory remains open.
-/

namespace BB6.Agent49FastSpectrum
open BB6.Agent49FullSpectrum
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

def down (xs : List Nat) : List Nat :=
  xs.filterMap (fun x => if x=0 then none else some (x-1))

theorem mem_down (xs : List Nat) (a : Nat) :
    a ∈ down xs ↔ a+1 ∈ xs := by
  simp only [down, List.mem_filterMap]
  constructor
  · rintro ⟨x,hx,hh⟩
    by_cases hz : x=0
    · simp [hz] at hh
    · simp [hz] at hh
      have : x=a+1 := by omega
      simpa [this] using hx
  · intro h
    refine ⟨a+1,h,?_⟩
    simp

/-- The compact all-first-counter failure list, computed by a single chain
of smaller quotient block counts, with an extra membership check at most. -/
def fastSpectrum (b : Nat) : List Nat :=
  if b=0 then []
  else if b%3=0 then down (fastSpectrum (b/3-1))
  else if b%3=1 then 0::(fastSpectrum (b/3)).map Nat.succ
  else (if badAll 0 (b/3) then [0] else []) ++
      (fastSpectrum (b/3+1)).map Nat.succ
termination_by b
decreasing_by all_goals omega

theorem mem_succ (xs : List Nat) (a : Nat) :
    a ∈ xs.map Nat.succ ↔ 0<a ∧ a-1 ∈ xs := by
  rw [List.mem_map]
  constructor
  · rintro ⟨x,hx,he⟩
    have hp : a=x+1 := by omega
    constructor
    · omega
    · have : x=a-1 := by omega
      simpa only [←this] using hx
  · rintro ⟨ha,hmem⟩
    refine ⟨a-1,hmem,?_⟩
    omega

theorem mem_optzero (p : Bool) (a : Nat) :
    a ∈ (if p then [0] else []) ↔ a=0 ∧ p=true := by
  cases p <;> simp

/-- Complete (unbounded) correctness: all natural first counters a appear
if and only if the original full B-drain fails at a. -/
theorem fastSpectrum_correct (b : Nat) :
    ∀ a, a ∈ fastSpectrum b ↔ badAll a b = true := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a
    conv => lhs; rw [fastSpectrum]
    conv => rhs; rw [badAll]
    by_cases hz : b=0
    · simp [hz]
    · simp only [if_neg hz]
      by_cases h0 : b%3=0
      · simp only [if_pos h0]
        rw [mem_down]
        exact ih (b/3-1) (by omega) (a+1)
      · simp only [if_neg h0]
        by_cases h1 : b%3=1
        · simp only [if_pos h1, List.mem_cons, mem_succ]
          by_cases ha : a=0
          · simp [ha]
          · simp only [if_neg ha]
            rw [ih (b/3) (by omega) (a-1)]
            simp [ha, Nat.pos_of_ne_zero ha]
        · simp only [if_neg h1, List.mem_append, mem_optzero, mem_succ]
          by_cases ha : a=0
          · simp [ha]
          · simp only [if_neg ha]
            rw [ih (b/3+1) (by omega) (a-1)]
            simp [ha, Nat.pos_of_ne_zero ha]

/-- The complete original-source drain failure spectrum, for all a,b,d. -/
theorem drain_none_iff_fastSpectrum (a b d : Nat) :
    (drainB a b d = none) ↔ a ∈ fastSpectrum b := by
  rw [drain_none_iff_badAll]
  exact (fastSpectrum_correct b a).symm

#print axioms fastSpectrum_correct
#print axioms drain_none_iff_fastSpectrum
end BB6.Agent49FastSpectrum
