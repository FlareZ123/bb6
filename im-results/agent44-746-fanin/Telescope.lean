import Std
set_option maxHeartbeats 0
namespace CascadeAgent44

def sameLogCount (f : Nat → Nat) (n : Nat) : Nat :=
  (List.range n).countP (fun i => decide (f i = f (i+1)))

/-- Every one-step decline of size zero or one has a count of plateaux
    determined exactly by its end values, without any enumeration. -/
theorem sameLogCount_telescope (f : Nat → Nat)
    (h : ∀i, f (i+1) ≤ f i ∧ f i ≤ f (i+1)+1) (n : Nat) :
    sameLogCount f n + f 0 = n + f n := by
  induction n with
  | zero => simp [sameLogCount]
  | succ n ih =>
    have hs : sameLogCount f (n+1) =
        sameLogCount f n + if f n = f (n+1) then 1 else 0 := by
      simp [sameLogCount, List.range_succ, List.countP_append]
    rw [hs]
    by_cases he : f n = f (n+1)
    · simp [he]
      omega
    · have hstep := h n
      have hplus : f n = f (n+1)+1 := by omega
      simp [he]
      omega

/-- Bounded form, suitable for a finite geometrically decreasing sequence. -/
theorem sameLogCount_telescope_bounded (f : Nat → Nat) (n : Nat)
    (h : ∀i, i<n → f (i+1) ≤ f i ∧ f i ≤ f (i+1)+1) :
    sameLogCount f n + f 0 = n + f n := by
  induction n with
  | zero => simp [sameLogCount]
  | succ n ih =>
    have hsmall : ∀ i, i<n → f (i+1) ≤ f i ∧ f i ≤ f (i+1)+1 := by
      intro i hi
      exact h i (by omega)
    have hprev := ih hsmall
    have hs : sameLogCount f (n+1) =
        sameLogCount f n + if f n = f (n+1) then 1 else 0 := by
      simp [sameLogCount, List.range_succ, List.countP_append]
    rw [hs]
    by_cases he : f n = f (n+1)
    · simp [he]
      omega
    · have hstep := h n (by omega)
      have hplus : f n = f (n+1)+1 := by omega
      simp [he]
      omega

#print axioms sameLogCount_telescope_bounded
#print axioms sameLogCount_telescope
end CascadeAgent44
