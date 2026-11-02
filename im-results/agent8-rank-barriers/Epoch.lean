import Sweep

namespace BB6Rank

/-- Compose two sequential Option-valued iteration intervals. -/
theorem runForward_add {α:Type} (f:α→Option α) (m n:Nat) (s:α) :
    runForward f (m+n) s = (runForward f m s).bind (runForward f n) := by
  induction m generalizing s with
  | zero => simp [runForward]
  | succ m ih =>
      simp only [Nat.succ_add, runForward]
      cases hs : f s with
      | none => simp [hs]
      | some t =>
          simp only [hs, Option.bind_some]
          exact ih t

private theorem c3_first_three (A k:Nat) :
    runForward nextC 3 (A+2*k+6,k,3) = some (A+2*k+4,1,2*k+7) := by
  simp only [runForward, nextC, Option.bind_some]
  congr 1 <;> omega

/-- Return to c=3 after an exactly known 2k+7 macro steps. -/
theorem nextC_c3_epoch (A k:Nat) :
    runForward nextC (2*k+7) (A+2*k+6,k,3) = some (A,2*k+5,3) := by
  have hn : 2*k+7 = 3 + (2*k+4) := by omega
  rw [hn, runForward_add]
  rw [c3_first_three]
  have hs := nextC_sweep (2*k+4) (A+2*k+4) 1 (2*k+7) (by omega) (by omega)
  have he : (A+2*k+4 - (2*k+4), 1+(2*k+4), 2*k+7-(2*k+4)) =
    (A,2*k+5,3) := by
      simp only [Prod.mk.injEq]
      omega
  rw [he] at hs
  exact hs

end BB6Rank

namespace BB6Rank

/-- Whole-epoch transfer with an even stack counter. -/
theorem nextC_even_transfer (j d : Nat) :
    runForward nextC (4*j+3) (0,2*j,d+4*j+8) = some (0,4*j+4,d+3) := by
  have hn : 4*j+3 = 1+(4*j+2) := by omega
  rw [hn, runForward_add]
  have hfirst : runForward nextC 1 (0,2*j,d+4*j+8) =
      some (4*j+2,2,d+4*j+5) := by
    have hmod : (2*j)%2=0 := by omega
    simp only [runForward, nextC]
    simp [hmod]
  rw [hfirst]
  have hs := nextC_sweep (4*j+2) (4*j+2) 2 (d+4*j+5) (by omega) (by omega)
  have he : (4*j+2 - (4*j+2), 2+(4*j+2), d+4*j+5-(4*j+2)) =
    (0,4*j+4,d+3) := by
      simp only [Prod.mk.injEq]
      omega
  rw [he] at hs
  exact hs

/-- Whole-epoch transfer with an odd stack counter. -/
theorem nextC_odd_transfer (j d : Nat) :
    runForward nextC (4*j+6) (0,2*j+1,d+4*j+8) = some (0,4*j+5,d+3) := by
  have hn : 4*j+6 = 1+(4*j+5) := by omega
  rw [hn, runForward_add]
  have hfirst : runForward nextC 1 (0,2*j+1,d+4*j+8) =
      some (4*j+5,0,d+4*j+8) := by
    have hmod : (2*j+1)%2≠0 := by omega
    simp only [runForward, nextC]
    simp [hmod]
    omega
  rw [hfirst]
  have hs := nextC_sweep (4*j+5) (4*j+5) 0 (d+4*j+8) (by omega) (by omega)
  have he : (4*j+5 - (4*j+5), 0+(4*j+5), d+4*j+8-(4*j+5)) =
    (0,4*j+5,d+3) := by
      simp only [Prod.mk.injEq]
      omega
  rw [he] at hs
  exact hs

end BB6Rank
