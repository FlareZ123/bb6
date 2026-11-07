import NeedleCubicBound
import NeedleTerminalDichotomy
import Lean.Elab.Tactic.Omega

namespace NeedleQuadraticEnum
open NeedleInverse

/-- Pair each valuation with its unique exact inverse quotient, when it exists. -/
def candidatePairs (K : Nat) (vs : List Nat) : List (Nat × Nat) :=
  vs.filterMap fun v => (candidate v K).map fun q => (v,q)

theorem candidatePairs_spec (q v K : Nat) (vs : List Nat) :
    (v,q) ∈ candidatePairs K vs ↔ v ∈ vs ∧ equation q v K := by
  rw [candidatePairs, List.mem_filterMap]
  constructor
  · rintro ⟨v',hv',hc⟩
    cases hq : candidate v' K with
    | none => simp [hq] at hc
    | some q' =>
      have hp : (v',q')=(v,q) := by simpa [hq] using hc
      obtain ⟨hv,hq'⟩ := Prod.mk.inj hp
      subst v'
      subst q'
      exact ⟨hv',(candidate_correct q v K).mp hq⟩
  · rintro ⟨hv',heq⟩
    refine ⟨v,hv',?_⟩
    simp [(candidate_correct q v K).mpr heq]

/-- Search the logarithmically many possible cancellation parameters,
    but evaluate an expensive inverse candidate only when the exact
    parameter identity K+1 = r*(9^r+5) holds. -/
def cancellationValuations (K : Nat) : List Nat :=
  (List.range (Nat.log2 (K+1)+1)).filterMap fun r =>
    if K+1 = r*(9^r+5) then
      let v := (9^r+3)/2
      if 11 ≤ v then some v else none
    else none

/-- Valuations below eleven, square-bounded valuations, and the exact
    cancellation family. -/
def quadraticValuations (K : Nat) : List Nat :=
  List.range 11 ++
    (List.filter (fun v => decide (11 ≤ v))
      (List.range (Nat.sqrt (8*(K+1))+1)) ++ cancellationValuations K)

def quadraticParents (K : Nat) : List (Nat × Nat) :=
  candidatePairs K (quadraticValuations K)

private theorem le_sqrt_of_sq_le (x v : Nat) (h : v*v ≤ x) :
    v ≤ Nat.sqrt x := by
  by_cases hle : v ≤ Nat.sqrt x
  · exact hle
  · have hs : Nat.sqrt x + 1 ≤ v := by omega
    have hmul := Nat.mul_le_mul hs hs
    have hlt : x < (Nat.sqrt x+1)*(Nat.sqrt x+1) := by
      simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt x
    omega

private theorem equation_to_terminal_feed (q v K : Nat)
    (h : equation q v K) :
    2^(K+1)+3 = (2^(v+1)+3)*(2*q+3)+2*v := by
  have hpow : 2^K = den v*q+bias v :=
    (equation_affine q v K).mp h
  have hiden : 2*bias v+3=3*den v+2*v := by
    simp [bias,den,Nat.pow_succ',Nat.mul_add] <;> omega
  calc
    2^(K+1)+3 = 2^K*2+3 := by rw [Nat.pow_succ]
    _ = (den v*q+bias v)*2+3 := by rw [hpow]
    _ = 2*den v*q+(2*bias v+3) := by
      simp [Nat.add_mul,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    _ = 2*den v*q+(3*den v+2*v) := by rw [hiden]
    _ = den v*(2*q+3)+2*v := by
      rw [Nat.mul_add]
      simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    _ = (2^(v+1)+3)*(2*q+3)+2*v := by rfl

private theorem cancellation_bound_log (v K : Nat)
    (hcancel : (K+1)%(v+1)=0 ∧ ((K+1)/(v+1))%2=0 ∧
      2*v=3^((K+1)/(v+1))+3) :
    ∃ r, r ≤ Nat.log2 (K+1) ∧ v=(9^r+3)/2 ∧
      K+1=r*(9^r+5) := by
  let n := (K+1)/(v+1)
  let r := n/2
  have hn : n=2*r := by
    dsimp [r]
    have h := Nat.mod_add_div n 2
    omega
  have hpow : 3^n=9^r := by
    rw [hn,Nat.pow_mul,show 3^2=9 by decide]
  have hv2 : 2*v=9^r+3 := by
    simpa [n,hpow] using hcancel.2.2
  have hvExpr : v=(9^r+3)/2 := by omega
  have hdecomp : K+1=(v+1)*n := by
    have h := (Nat.mod_add_div (K+1) (v+1)).symm
    simpa [hcancel.1,n] using h
  have htwov : 2*(v+1)=9^r+5 := by omega
  have hK : K+1=r*(9^r+5) := by
    calc
      K+1=(v+1)*(2*r) := by simpa [hn] using hdecomp
      _=r*(2*(v+1)) := by simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
      _=r*(9^r+5) := by rw [htwov]
  have hrpos : 1≤r := by
    by_cases hr : 1≤r
    · exact hr
    · have hr0 : r=0 := by omega
      rw [hr0] at hK
      omega
  have hpow2 : 2^r≤9^r :=
    Nat.pow_le_pow_left (by decide : 2≤9) r
  have hmul : 9^r≤r*(9^r+5) := by
    calc
      9^r=1*9^r := by simp
      _≤r*9^r := Nat.mul_le_mul_right (9^r) (by omega)
      _≤r*(9^r+5) := Nat.mul_le_mul_left r (by omega)
  have h2K : 2^r≤K+1 := by
    calc
      2^r≤9^r := hpow2
      _≤r*(9^r+5) := hmul
      _=K+1 := hK.symm
  have hrlog : r≤Nat.log2 (K+1) :=
    (Nat.le_log2 (by omega : K+1≠0)).mpr h2K
  exact ⟨r,hrlog,hvExpr,hK⟩

/-- Every exact terminal predecessor valuation occurs in the finite list. -/
theorem valuation_mem_quadraticValuations (q v K : Nat)
    (heq : equation q v K) : v ∈ quadraticValuations K := by
  unfold quadraticValuations
  by_cases hlow : v<11
  · exact List.mem_append.mpr (Or.inl (List.mem_range.mpr hlow))
  · have hv : 11≤v := by omega
    have hfeed := equation_to_terminal_feed q v K heq
    rcases NeedleTerminalDichotomy.terminal_exception_or_square_bound
      q v K hv hfeed with hcancel | hbound
    · rcases cancellation_bound_log v K hcancel with
        ⟨r,hrlog,hvExpr,hK⟩
      apply List.mem_append.mpr
      right
      apply List.mem_append.mpr
      right
      change v ∈ cancellationValuations K
      unfold cancellationValuations
      apply List.mem_filterMap.mpr
      refine ⟨r,List.mem_range.mpr (by omega),?_⟩
      have hv' : 11≤(9^r+3)/2 := by simpa [hvExpr] using hv
      simp [hK,hv',hvExpr]
    · have hsqrt := le_sqrt_of_sq_le (8*(K+1)) v hbound
      apply List.mem_append.mpr
      right
      apply List.mem_append.mpr
      left
      apply List.mem_filter.mpr
      exact ⟨List.mem_range.mpr (by omega),by simp [hv]⟩

/-- The executable valuation list is complete and sound for the exact
    terminal predecessor equation. -/
theorem quadraticParents_spec (q v K : Nat) :
    (v,q) ∈ quadraticParents K ↔ equation q v K := by
  rw [quadraticParents, candidatePairs_spec]
  constructor
  · rintro ⟨_,heq⟩
    exact heq
  · intro heq
    exact ⟨valuation_mem_quadraticValuations q v K heq,heq⟩

/-- Intersect the complete quadratic list with the already certified
    sixth-linear condition. This removes synthetic exceptional feeders that
    are excluded by the genuine blank-root theorem. -/
def quadraticRegularParents (K : Nat) : List (Nat × Nat) :=
  (quadraticParents K).filter fun p => decide (6*p.1 ≤ K+4)

theorem quadraticRegularParents_spec (q v K : Nat) :
    (v,q) ∈ quadraticRegularParents K ↔
      equation q v K ∧ 6*v ≤ K+4 := by
  rw [quadraticRegularParents, List.mem_filter]
  constructor
  · rintro ⟨hm,hb⟩
    exact ⟨(quadraticParents_spec q v K).mp hm, by simpa using hb⟩
  · rintro ⟨heq,hb⟩
    exact ⟨(quadraticParents_spec q v K).mpr heq, by simpa using hb⟩

/-- The list has at most O(sqrt(K)+log(K)) valuation trials, with an
    explicit bound independent of the quotient q. -/
theorem quadraticParents_length_bound (K : Nat) :
    (quadraticParents K).length ≤
      11 + (Nat.sqrt (8*(K+1))+1) + (Nat.log2 (K+1)+1) := by
  unfold quadraticParents candidatePairs
  calc
    _ ≤ (quadraticValuations K).length := List.length_filterMap_le _ _
    _ = 11 +
        ((List.filter (fun v => decide (11 ≤ v))
          (List.range (Nat.sqrt (8*(K+1))+1))).length +
        (cancellationValuations K).length) := by
            simp [quadraticValuations, List.length_append, List.length_range]
    _ ≤ 11 + (Nat.sqrt (8*(K+1))+1) + (Nat.log2 (K+1)+1) := by
      have hm := List.length_filter_le
        (fun v => decide (11 ≤ v))
        (List.range (Nat.sqrt (8*(K+1))+1))
      have he := List.length_filterMap_le
        (fun r => if K+1 = r*(9^r+5) then
          let v := (9^r+3)/2
          if 11 ≤ v then some v else none
          else none)
        (List.range (Nat.log2 (K+1)+1))
      have hm' : (List.filter (fun v => decide (11 ≤ v))
          (List.range (Nat.sqrt (8*(K+1))+1))).length ≤ Nat.sqrt (8*(K+1))+1 := by
        simpa [List.length_range] using hm
      have he' : (cancellationValuations K).length ≤ Nat.log2 (K+1)+1 := by
        simpa [cancellationValuations, List.length_range] using he
      omega

#eval (quadraticParents 13).map Prod.fst
#eval (quadraticParents 171).map Prod.fst
#eval (quadraticParents 2201).map Prod.fst

theorem quadraticRegularParents_length_bound (K : Nat) :
    (quadraticRegularParents K).length ≤
      11 + (Nat.sqrt (8*(K+1))+1) + (Nat.log2 (K+1)+1) := by
  unfold quadraticRegularParents
  calc
    _ ≤ (quadraticParents K).length := List.length_filter_le _ _
    _ ≤ 11 + (Nat.sqrt (8*(K+1))+1) + (Nat.log2 (K+1)+1) :=
      quadraticParents_length_bound K

#print axioms quadraticParents_spec
#print axioms quadraticParents_length_bound
#print axioms quadraticRegularParents_spec
#print axioms quadraticRegularParents_length_bound
end NeedleQuadraticEnum
