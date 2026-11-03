import BB429Rank
import Lean.Elab.Tactic.Omega

/-!
A genuine infinite family of nonhalting accelerated states for six-state #429.
The BB429 next/run definitions are imported unchanged from Agent5's
source-transcribed transition module. This theorem does not prove blank
reachability of any member of the family.
-/
namespace BB429Escape
open BB429

theorem step1 (u : Nat) (hlo : 17 ≤ u) (hmod : u % 4 = 1) :
    next (u,u+8) = some ((u-1)/2,2*u+16) := by
  have h0 : ¬ u+8 ≥ 2*u+3 := by omega
  have h1 : u+8 ≠ 2*u+2 := by omega
  have h2 : u+8 ≠ 2*u+1 := by omega
  have h3 : u+8 ≠ 2*u := by omega
  have he : (u+8)%2 ≠ 0 := by omega
  have hd1 : u-(u+8)/2 ≠ 1 := by omega
  have hd2 : u-(u+8)/2 ≠ 2 := by omega
  have hd3 : (u-(u+8)/2)%2 ≠ 0 := by omega
  simp [next,h0,h1,h2,h3,he,hd1,hd2,hd3]
  omega

theorem step2 (u : Nat) (_hlo : 17 ≤ u) (hmod : u % 4 = 1) :
    next ((u-1)/2,2*u+16) = some (u+2,u+14) := by
  have h : 2*u+16 ≥ 2*((u-1)/2)+3 := by omega
  simp [next,h]
  omega

theorem step3 (u : Nat) (hlo : 17 ≤ u) (hmod : u % 4 = 1) :
    next (u+2,u+14) = some ((u+5)/2,2*u+24) := by
  have h0 : ¬ u+14 ≥ 2*(u+2)+3 := by omega
  have h1 : u+14 ≠ 2*(u+2)+2 := by omega
  have h2 : u+14 ≠ 2*(u+2)+1 := by omega
  have h3 : u+14 ≠ 2*(u+2) := by omega
  have he : (u+14)%2 ≠ 0 := by omega
  have hd1 : (u+2)-(u+14)/2 ≠ 1 := by omega
  have hd2 : (u+2)-(u+14)/2 ≠ 2 := by omega
  have hd3 : ((u+2)-(u+14)/2)%2 = 0 := by omega
  have hw : u+14 ≠ 1 := by omega
  simp [next,h0,h1,h2,h3,he,hd1,hd2,hd3,hw]
  omega

theorem step4 (u : Nat) (hlo : 17 ≤ u) (hmod : u % 4 = 1) :
    next ((u+5)/2,2*u+24) = some (u+8,u+16) := by
  have h : 2*u+24 ≥ 2*((u+5)/2)+3 := by omega
  simp [next,h]
  omega

theorem run4 (u : Nat) (hlo : 17 ≤ u) (hmod : u % 4 = 1) :
    run 4 (u,u+8) = some (u+8,u+16) := by
  simp only [run, Option.bind_some, step1 u hlo hmod,
    step2 u hlo hmod, step3 u hlo hmod, step4 u hlo hmod]

theorem run_add (n k : Nat) (s : State) :
    run (n+k) s = (run n s).bind (run k) := by
  induction k with
  | zero => simp [run]
  | succ k ih =>
    rw [Nat.add_succ]
    simp only [run, ih]
    cases h : run n s with
    | none => simp
    | some t => simp [run]

theorem line_iter (u n : Nat) (hlo : 17 ≤ u) (hmod : u % 4 = 1) :
    run (4*n) (u,u+8) = some (u+8*n,u+8*n+8) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    have hlo2 : 17 ≤ u+8*n := by omega
    have hm2 : (u+8*n)%4=1 := by omega
    have h4 := run4 (u+8*n) hlo2 hm2
    rw [show 4*(n+1)=4*n+4 by omega, run_add, ih]
    simp only [Option.bind_some]
    rw [h4]
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor <;> omega

theorem run_prefix (s : State) (n m : Nat)
    (h : run (n+m) s ≠ none) : run n s ≠ none := by
  rw [run_add] at h
  cases hn : run n s with
  | none => simp [hn] at h
  | some t => simp

/-- Every accelerated configuration on this ray survives all future steps. -/
theorem line_never (u n : Nat) (hlo : 17 ≤ u) (hmod : u % 4 = 1) :
    run n (u,u+8) ≠ none := by
  have hlong : run (n+3*n) (u,u+8) ≠ none := by
    have hi := line_iter u n hlo hmod
    simp only [show n+3*n=4*n by omega, hi, ne_eq, reduceCtorEq, not_false_eq_true]
  exact run_prefix (u,u+8) n (3*n) hlong

/-- A proven entry from any starting state transfers all-time survival. -/
theorem line_entry_never (start : State) (u t n : Nat)
    (hlo : 17 ≤ u) (hmod : u % 4 = 1)
    (hentry : run t start = some (u,u+8)) : run n start ≠ none := by
  by_cases hnt : n ≤ t
  · have hlong : run (n+(t-n)) start ≠ none := by
      have heq : n+(t-n)=t := by omega
      rw [heq,hentry]
      simp
    exact run_prefix start n (t-n) hlong
  · have htn : t ≤ n := by omega
    have heq : n=t+(n-t) := by omega
    rw [heq,run_add,hentry]
    simpa using line_never u (n-t) hlo hmod

#print axioms line_entry_never
#print axioms line_iter
#print axioms line_never
#print axioms step1
#print axioms step2
#print axioms step3
#print axioms step4
#print axioms run4
end BB429Escape
