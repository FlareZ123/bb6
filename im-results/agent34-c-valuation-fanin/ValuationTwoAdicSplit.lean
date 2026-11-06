import ValuationDegreeBound
import Lean.Elab.Tactic.Omega

namespace BB6.Agent34Valuation
open BB6.Agent46

/-- Computable decomposition of a natural number into its 2-adic
valuation and its remaining odd factor. The second component is the
odd factor itself, not its half. -/
def twoAdicSplit : Nat → Nat × Nat
| 0 => (0,0)
| n+1 =>
    if (n+1)%2=0 then
      let d := twoAdicSplit ((n+1)/2)
      (d.1+1,d.2)
    else (0,n+1)
termination_by n => n
decreasing_by
  simp_wf
  omega

theorem twoAdicSplit_spec : ∀ n, 0<n →
    n=2^(twoAdicSplit n).1*(twoAdicSplit n).2 ∧
    (twoAdicSplit n).2%2=1 := by
  intro n
  refine Nat.strongRecOn n ?_
  intro n ih hn
  cases n with
  | zero => omega
  | succ m =>
    by_cases he : (m+1)%2=0
    · have hlt : (m+1)/2 < m+1 := by omega
      obtain ⟨hdecomp,hodd⟩ := ih ((m+1)/2) hlt (by omega)
      constructor
      · have hmul : m+1=2*((m+1)/2) := by
          have hdiv := Nat.mod_add_div (m+1) 2
          omega
        calc
          m+1=2*((m+1)/2) := hmul
          _=2*(2^(twoAdicSplit ((m+1)/2)).1*(twoAdicSplit ((m+1)/2)).2) :=
            congrArg (fun z => 2*z) hdecomp
          _=2^(twoAdicSplit ((m+1)/2)).1.succ*
              (twoAdicSplit ((m+1)/2)).2 := by
            simp [Nat.pow_succ]
            ac_rfl
          _=2^(twoAdicSplit (m+1)).1*(twoAdicSplit (m+1)).2 := by
            simp [twoAdicSplit,he]
      · simp [twoAdicSplit,he,hodd]
    · have hodd : (m+1)%2=1 := by omega
      constructor
      · have hmul : m+1=2*(m/2)+1 := by
          have hdiv := Nat.mod_add_div (m+1) 2
          omega
        simp [twoAdicSplit,hodd]
      · simp [twoAdicSplit,hodd]

theorem twoAdicSplit_factor (n : Nat) (hn : 0<n) :
    n=2^(twoAdicSplit n).1*
      (2*(((twoAdicSplit n).2-1)/2)+1) := by
  obtain ⟨hdecomp,hodd⟩ := twoAdicSplit_spec n hn
  have hfactor : (twoAdicSplit n).2=
      2*(((twoAdicSplit n).2-1)/2)+1 := by omega
  rw [hfactor] at hdecomp
  exact hdecomp

def valuationFullCandidates (x y : Nat) : List (Nat × Nat) :=
  if (x+y)%2=0 then
    let d := twoAdicSplit (x+y)
    let u := (d.2-1)/2
    evenFullCandidates x y d.1 u
  else
    let d := twoAdicSplit (x+y+1)
    let u := (d.2-1)/2
    oddFullCandidates x y d.1 u

theorem parent_mem_valuationFullCandidates (a k x y : Nat)
    (hy : 5≤y) (hedge : secNext (a,k)=some (x,y)) :
    (a,k)∈valuationFullCandidates x y := by
  by_cases hS : (x+y)%2=0
  · let d := twoAdicSplit (x+y)
    let u := (d.2-1)/2
    have hfact : x+y=2^d.1*(2*u+1) := by
      simpa [d,u] using twoAdicSplit_factor (x+y) (by omega)
    have hmem := even_sum_parent_mem_fullCandidates a k x y d.1 u
      hy hS hfact hedge
    simpa [valuationFullCandidates,hS,d,u] using hmem
  · have hSodd : (x+y)%2=1 := by
      have hmod := Nat.mod_two_eq_zero_or_one (x+y)
      omega
    let d := twoAdicSplit (x+y+1)
    let u := (d.2-1)/2
    have hfact : x+y+1=2^d.1*(2*u+1) := by
      simpa [d,u] using twoAdicSplit_factor (x+y+1) (by omega)
    have hmem := odd_sum_parent_mem_fullCandidates a k x y d.1 u
      hy hSodd hfact hedge
    simpa [valuationFullCandidates,hS,d,u] using hmem

theorem valuationFullCandidates_length_bound (x y : Nat)
    (hy : 5≤y) :
    (valuationFullCandidates x y).length ≤
      (if (x+y)%2=0 then
        (twoAdicSplit (x+y)).1/2+1
       else
        (twoAdicSplit (x+y+1)).1/2+1) := by
  by_cases hS : (x+y)%2=0
  · let d := twoAdicSplit (x+y)
    let u := (d.2-1)/2
    have hfact : x+y=2^d.1*(2*u+1) := by
      simpa [d,u] using twoAdicSplit_factor (x+y) (by omega)
    simpa [valuationFullCandidates,hS,d,u] using
      evenFullCandidates_length_bound x y d.1 u hy hfact
  · have hSodd : (x+y)%2=1 := by
      have hmod := Nat.mod_two_eq_zero_or_one (x+y)
      omega
    let d := twoAdicSplit (x+y+1)
    let u := (d.2-1)/2
    have hfact : x+y+1=2^d.1*(2*u+1) := by
      simpa [d,u] using twoAdicSplit_factor (x+y+1) (by omega)
    simpa [valuationFullCandidates,hS,d,u,hSodd] using
      oddFullCandidates_length_bound x y d.1 u hy hfact

#print axioms twoAdicSplit_spec
#print axioms parent_mem_valuationFullCandidates
#print axioms valuationFullCandidates_length_bound

end BB6.Agent34Valuation
