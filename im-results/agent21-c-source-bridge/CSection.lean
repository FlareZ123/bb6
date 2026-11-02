import Lean.Elab.Tactic.Omega
import CReachBridge

namespace BB6.CSection
open CReachBridge

/-- Exact composition of finite accelerated traces. -/
theorem runN_add (n m : Nat) (s : Option S) :
    runN (n+m) s = runN m (runN n s) := by
  induction m with
  | zero => simp [runN]
  | succ m ih =>
      rw [Nat.add_succ]
      change stepC (runN (n+m) s) = stepC (runN m (runN n s))
      rw [ih]

/-- An arbitrary high-counter sweep has an exact number of transitions. -/
theorem sweep (q a k d : Nat) :
    runN q (some (a+q,k,d+q+3)) = some (a,k+q,d+3) := by
  induction q generalizing k with
  | zero => simp [runN]
  | succ q ih =>
      have hs : stepC (some (a+(q+1),k,d+(q+1)+3)) =
          some (a+q,k+1,d+q+3) := by
        have h1 : a+(q+1) = (a+q)+1 := by omega
        have h2 : d+(q+1)+3 = (d+q)+4 := by omega
        rw [h1,h2]
        rfl
      rw [runN_succ_head, hs]
      have he : k+1+q = k+(q+1) := by omega
      simpa only [he] using ih (k+1)

/-- Exact first-return on the c=0 section above the line a=2k, for k>=1.
    The return occurs after 2k+1 accelerated steps, independently of surplus r. -/
theorem section_long (k r : Nat) :
    runN (2*(k+1)+1) (some (2*(k+1)+r,k+1,0)) =
      some (r,2*(k+1)+2,0) := by
  have hfirst : stepC (some (2*(k+1)+r,k+1,0)) =
      some (r+2*k,1,2*k+3) := by
    have he : 2*(k+1)+r = (r+2*k)+2 := by omega
    rw [he]
    simp only [stepC, Option.bind_some]
    change BB6CLine.nextC ((r+2*k)+2,k+1,0) =
      some (r+2*k,1,2*k+3)
    have hc : 2*(k+1)+1 = 2*k+3 := by omega
    simpa only [hc] using (show BB6CLine.nextC ((r+2*k)+2,k+1,0) =
      some (r+2*k,1,2*(k+1)+1) from rfl)
  have htail : runN 2 (some (r,1+2*k,3)) = some (r,2*k+4,0) := by
    simp [runN,stepC,BB6CLine.nextC]
    omega
  have htotal : 2*(k+1)+1 = (2*k+2)+1 := by omega
  rw [htotal,runN_succ_head,hfirst]
  rw [show 2*k+2=(2*k)+2 by omega, runN_add (2*k) 2]
  have hs := sweep (2*k) r 1 0
  simp only [Nat.zero_add] at hs
  rw [hs,htail]
  congr 1

/-- Exact first short-sector excursion from a zero-right-counter state.
    The parameter equation 2k=e+q+3 ensures the high sweep ends at c=e+4. -/
theorem section_short (q k e : Nat) (h : 2*k=e+q+3) :
    runN (q+2) (some (q+2,k,0)) =
      if (q+1)%2=0 then some (4*((q+1)/2)+2,2,e+1)
        else some (4*((q+1)/2)+5,0,e+4) := by
  have hf : stepC (some (q+2,k,0)) = some (q,1,(e+1)+q+3) := by
    change BB6CLine.nextC (q+2,k,0) = some (q,1,e+1+q+3)
    have he : 2*k+1=e+1+q+3 := by omega
    simpa only [he] using
      (show BB6CLine.nextC (q+2,k,0) = some (q,1,2*k+1) from rfl)
  have hs := sweep q 0 1 (e+1)
  simp only [Nat.zero_add] at hs
  have hx : stepC (some (0,q+1,e+4)) =
      if (q+1)%2=0 then some (4*((q+1)/2)+2,2,e+1)
        else some (4*((q+1)/2)+5,0,e+4) := by
    rfl
  rw [show q+2=(q+1)+1 by omega, runN_succ_head, hf]
  rw [runN_add q 1, hs]
  change stepC (some (0,1+q,e+1+3)) = _
  simpa only [show 1+q=q+1 by omega, show e+1+3=e+4 by omega] using hx


/-- An odd a below 2k follows the even-k zero-left branch. -/
theorem section_short_odd (m k e : Nat) (h : 2*k=e+2*m+4) :
    runN (2*m+3) (some (2*m+3,k,0)) = some (4*m+6,2,e+1) := by
  have h' : 2*k=e+(2*m+1)+3 := by omega
  have hs := section_short (2*m+1) k e h'
  have htime : (2*m+1)+2 = 2*m+3 := by omega
  have hpar : ((2*m+1)+1)%2=0 := by omega
  rw [htime] at hs
  simp only [hpar, ↓reduceIte] at hs
  have hdiv : ((2*m+1)+1)/2=m+1 := by omega
  rw [hdiv] at hs
  simpa only [show 4*(m+1)+2=4*m+6 by omega] using hs

/-- An even a below 2k follows the odd-k zero-left branch. -/
theorem section_short_even (m k e : Nat) (h : 2*k=e+2*m+3) :
    runN (2*m+2) (some (2*m+2,k,0)) = some (4*m+5,0,e+4) := by
  have hs := section_short (2*m) k e (by omega)
  have hpar : ((2*m)+1)%2≠0 := by omega
  simp only [hpar, ↓reduceIte] at hs
  have hdiv : ((2*m)+1)/2=m := by omega
  rw [hdiv] at hs
  exact hs

#print axioms section_long
#print axioms section_short
#print axioms section_short_odd
#print axioms section_short_even
end BB6.CSection
