import CReachBridge
import Lean.Elab.Tactic.Omega

namespace BB6.CRange
open BB6.CReachBridge

/-- Two universal modular constraints on the nonreset stages of each phase. -/
def good : S → Prop
  | (a,k,c) =>
      (3 ≤ c → (k+c)%2=0 ∨ (a+k)%4=0 ∨ (a+k)%4=1) ∧
      (c=1 → 4 ≤ k → k%2=0 → (a+k)%4=2 ∨ (a+k)%4=3)

theorem good_preserved (s t : S)
    (hg : good s) (h : BB6CLine.nextC s=some t) : good t := by
  rcases s with ⟨a,k,c⟩
  rcases c with _ | _ | _ | _ | d
  · rcases a with _ | _ | a
    · simp only [BB6CLine.nextC, Option.some.injEq] at h
      subst t
      simp [good] <;> omega
    · rcases k with _ | k
      · simp only [BB6CLine.nextC, Option.some.injEq] at h
        subst t
        simp [good]
      · simp only [BB6CLine.nextC, Option.some.injEq] at h
        subst t
        simp [good] <;> omega
    · simp only [BB6CLine.nextC, Option.some.injEq] at h
      subst t
      simp [good] <;> omega
  · simp only [BB6CLine.nextC, Option.some.injEq] at h
    subst t
    simp [good]
  · simp [BB6CLine.nextC] at h
  · simp only [BB6CLine.nextC, Option.some.injEq] at h
    subst t
    simp only [good] at hg ⊢
    constructor
    · omega
    · intro h1 hk hp
      have hc := hg.1 (by omega)
      omega
  · rcases a with _ | a
    · by_cases hk:k%2=0
      · simp only [BB6CLine.nextC,hk,↓reduceIte,Option.some.injEq] at h
        subst t
        simp [good] <;> omega
      · simp only [BB6CLine.nextC,hk,↓reduceIte,Option.some.injEq] at h
        subst t
        simp [good] <;> omega
    · simp only [BB6CLine.nextC, Option.some.injEq] at h
      subst t
      simp only [good] at hg ⊢
      constructor
      · intro hc
        have gh := hg.1 (by omega)
        omega
      · intro hc
        omega

theorem good_run (a k n : Nat) (s : S)
    (h : runN n (some (a,k,0)) = some s) : good s := by
  induction n generalizing s with
  | zero =>
      simp [runN] at h
      subst s
      simp [good]
  | succ n ih =>
      change (runN n (some (a,k,0))).bind BB6CLine.nextC = some s at h
      cases hp : runN n (some (a,k,0)) with
      | none => simp [hp] at h
      | some p =>
          rw [hp] at h
          change BB6CLine.nextC p = some s at h
          exact good_preserved p s (ih p hp) h

/-- A predecessor satisfying good cannot output an odd reset of residue 1 or 2. -/
theorem good_last (s : S) (A K : Nat)
    (hg : good s) (h : BB6CLine.nextC s=some (A,K,0))
    (hK : 5 ≤ K) (hodd : K%2=1) :
    (A+K)%4=0 ∨ (A+K)%4=3 := by
  rcases s with ⟨a,k,c⟩
  rcases c with _ | _ | _ | _ | d
  · rcases a with _ | _ | a
    · simp [BB6CLine.nextC] at h
    · rcases k with _ | k <;> simp [BB6CLine.nextC] at h
    · simp [BB6CLine.nextC] at h
  · simp only [BB6CLine.nextC,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨ha,hk,hc⟩
    subst A
    subst K
    simp only [good] at hg
    have hkbound : 4 ≤ k := by omega
    have hkeven : k%2=0 := by omega
    have hg2 := hg.2 trivial hkbound hkeven
    omega
  · simp [BB6CLine.nextC] at h
  · simp [BB6CLine.nextC] at h
  · rcases a with _ | a
    · by_cases hk:k%2=0 <;> simp [BB6CLine.nextC,hk] at h
    · simp [BB6CLine.nextC] at h

/-- Universal all-time c=0 return range hole from any initial c=0 counters. -/
theorem zero_return_mod4_hole (a k A K n : Nat)
    (h : runN (n+1) (some (a,k,0))=some (A,K,0))
    (hK : 5 ≤ K) (hodd : K%2=1) :
    (A+K)%4=0 ∨ (A+K)%4=3 := by
  change (runN n (some (a,k,0))).bind BB6CLine.nextC = some (A,K,0) at h
  cases hp:runN n (some (a,k,0)) with
  | none => simp [hp] at h
  | some s =>
      rw [hp] at h
      change BB6CLine.nextC s = some (A,K,0) at h
      exact good_last s A K (good_run a k n s hp) h hK hodd

#print axioms good_preserved
#print axioms zero_return_mod4_hole
end BB6.CRange
