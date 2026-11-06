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

theorem directExactCandidates_sound (x y : Nat) (p : Nat × Nat)
    (hp : p∈directExactCandidates x y) :
    secNext p=some (x,y) := by
  unfold directExactCandidates at hp
  by_cases h : y%2=0 ∧
      secNext (x+y-2,(y-2)/2)=some (x,y)
  · simp only [if_pos h,List.mem_singleton] at hp
    subst p
    exact h.2
  · simp [h] at hp

theorem zeroExactCandidates_sound (x y v u : Nat)
    (p : Nat × Nat) (hp : p∈zeroExactCandidates x y v u) :
    secNext p=some (x,y) := by
  unfold zeroExactCandidates at hp
  by_cases h : u=0 ∧ 3≤v ∧
      secNext (zeroParentAtValuation x y v)=some (x,y)
  · simp only [if_pos h,List.mem_singleton] at hp
    subst p
    exact h.2.2
  · simp [h] at hp

theorem oneExactCandidates_sound (x y v u : Nat)
    (p : Nat × Nat) (hp : p∈oneExactCandidates x y v u) :
    secNext p=some (x,y) := by
  unfold oneExactCandidates at hp
  by_cases h1 : u=0 ∧ 4≤v ∧
      secNext (oneParentAtValuation x y v)=some (x,y)
  · simp only [if_pos h1,List.mem_singleton] at hp
    subst p
    exact h1.2.2
  · by_cases h2 : x=2 ∧ y=5 ∧ secNext (1,2)=some (x,y)
    · simp only [if_neg h1,if_pos h2,List.mem_singleton] at hp
      subst p
      exact h2.2.2
    · by_cases h3 : x=0 ∧ y=7 ∧ secNext (1,3)=some (x,y)
      · simp only [if_neg h1,if_neg h2,if_pos h3,List.mem_singleton] at hp
        subst p
        exact h3.2.2
      · simp [h1,h2,h3] at hp

theorem evenHighExactCandidates_sound (x y v : Nat)
    (p : Nat × Nat) (hp : p∈evenHighExactCandidates x y v) :
    secNext p=some (x,y) := by
  simp only [evenHighExactCandidates,List.mem_filter,decide_eq_true_eq] at hp
  exact hp.2

theorem oddHighExactCandidates_sound (x y v : Nat)
    (p : Nat × Nat) (hp : p∈oddHighExactCandidates x y v) :
    secNext p=some (x,y) := by
  simp only [oddHighExactCandidates,List.mem_filter,decide_eq_true_eq] at hp
  exact hp.2

theorem evenFullCandidates_sound (x y v u : Nat)
    (p : Nat × Nat) (hp : p∈evenFullCandidates x y v u) :
    secNext p=some (x,y) := by
  unfold evenFullCandidates at hp
  rcases List.mem_append.mp hp with hhd | hz
  · rcases List.mem_append.mp hhd with hh | hd
    · exact evenHighExactCandidates_sound x y v p hh
    · exact directExactCandidates_sound x y p hd
  · exact zeroExactCandidates_sound x y v u p hz

theorem oddFullCandidates_sound (x y v u : Nat)
    (p : Nat × Nat) (hp : p∈oddFullCandidates x y v u) :
    secNext p=some (x,y) := by
  unfold oddFullCandidates at hp
  rcases List.mem_append.mp hp with hhd | hone
  · rcases List.mem_append.mp hhd with hh | hd
    · exact oddHighExactCandidates_sound x y v p hh
    · exact directExactCandidates_sound x y p hd
  · exact oneExactCandidates_sound x y v u p hone

theorem valuationFullCandidates_sound (x y : Nat)
    (p : Nat × Nat) (hp : p∈valuationFullCandidates x y) :
    secNext p=some (x,y) := by
  by_cases hS : (x+y)%2=0
  · let d := twoAdicSplit (x+y)
    let u := (d.2-1)/2
    have hp' : p∈evenFullCandidates x y d.1 u := by
      simpa [valuationFullCandidates,hS,d,u] using hp
    exact evenFullCandidates_sound x y d.1 u p hp'
  · let d := twoAdicSplit (x+y+1)
    let u := (d.2-1)/2
    have hp' : p∈oddFullCandidates x y d.1 u := by
      simpa [valuationFullCandidates,hS,d,u] using hp
    exact oddFullCandidates_sound x y d.1 u p hp'

/-- For y>=5, the valuation-indexed list is an exact executable
predecessor enumerator, not merely a cardinality-bounding superset. -/
theorem valuationFullCandidates_exact (a k x y : Nat)
    (hy : 5≤y) :
    (a,k)∈valuationFullCandidates x y ↔
      secNext (a,k)=some (x,y) := by
  constructor
  · exact valuationFullCandidates_sound x y (a,k)
  · exact parent_mem_valuationFullCandidates a k x y hy

#print axioms twoAdicSplit_spec
#print axioms parent_mem_valuationFullCandidates
#print axioms valuationFullCandidates_length_bound
#print axioms valuationFullCandidates_exact

end BB6.Agent34Valuation
