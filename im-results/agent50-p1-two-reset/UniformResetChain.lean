import UniformDefectStep
set_option maxHeartbeats 2000000

namespace BB6.Agent50TwoReset

/-- Explicit dyadic envelope after j additional positive resets. -/
def budget (n : Nat) : Nat → Nat
  | 0 => 24*(n+2)^3
  | j+1 => budget n j*(24*(n+2)^2)

/-- Exact source-shaped algebraic reset grammar. Its base post-first-reset
    defect and each transition are explicit hypotheses, and are not yet
    equivalent to original P1 CountCone histories. -/
inductive ResetChain (n K : Nat) : Nat → Nat → Nat → Nat → Prop where
  | base {m F D N C : Nat}
      (hbudget : 2^m ≤ budget n 0)
      (hNpos : 0<N) (hNbound : N≤n+m+1)
      (hC : C≤2^m)
      (hdefect : F+N=7*2^(n-m)*C)
      (hbalance : F+D+m=K+2) :
      ResetChain n K 0 m F D
  | step {j m F D l s Dp Fend Dend : Nat}
      (hprev : ResetChain n K j m F D)
      (hl : 2≤l)
      (hreset : 2^l*Dp+m=K+D)
      (hsuffix : 2^s*Fend+Dp+m+l=K+2)
      (hbalance : Fend+Dend+(m+l+s)=K+2) :
      ResetChain n K (j+1) (m+l+s) Fend Dend

private theorem budget_step_le (n j : Nat) : budget n j ≤ budget n (j+1) := by
  have hxpos : 0<n+2 := by omega
  have hx : 1≤(n+2)^2 := Nat.one_le_pow 2 (n+2) (by omega)
  have hf : 1≤24*(n+2)^2 := by omega
  have hh := Nat.mul_le_mul_left (budget n j) hf
  simpa only [budget, Nat.mul_one] using hh

/-- Uniform invariant for arbitrarily many exact algebraic positive resets,
    assuming the explicit polynomial envelope remains below 2^n. -/
theorem ResetChain.invariant
    {n K j m F D : Nat}
    (hn : 42≤n) (hK : K+n+3=7*2^n)
    (h : ResetChain n K j m F D)
    (hsmall : budget n j<2^n) :
    ∃ N C : Nat,
      0<N ∧ N≤n+m+1 ∧ C≤2^m ∧
      F+N=7*2^(n-m)*C ∧
      F+D+m=K+2 ∧
      2^m≤budget n j := by
  induction h with
  | @base m F D N C hbud hpos hbound hC hdef hbal =>
    exact ⟨N,C,hpos,hbound,hC,hdef,hbal,hbud⟩
  | @step j m F D l s Dp Fend Dend hp hl hreset hsuffix hbal ih =>
    have hstepSmall : budget n j*(24*(n+2)^2)<2^n := by
      simpa only [budget] using hsmall
    have hprevsmall : budget n j<2^n :=
      Nat.lt_of_le_of_lt (budget_step_le n j) hsmall
    obtain ⟨N,C,hpos,hbound,hC,hdef,hbalance,hbudget⟩ := ih hprevsmall
    let V := 2*2^m-C
    have hV : V+C=2*2^m := by dsimp [V]; omega
    obtain ⟨N2,C2,hN2pos,hN2bound,hC2,hdef2,hbudget2⟩ :=
      uniform_defect_step n m l s (budget n j) K D F N C V Dp Fend
        hn hbudget hstepSmall hpos hbound hK hV hdef hbalance
        hreset hl hsuffix
    refine ⟨N2,C2,hN2pos,hN2bound,hC2,hdef2,hbal,?_⟩
    simpa only [budget] using hbudget2

/-- General parameterized obstruction, conditional on exact reset grammar
    and the original-word logarithmic wall necessity. -/
theorem ResetChain.excludes_log_wall
    {n K j m F D : Nat}
    (hn : 42≤n) (hK : K+n+3=7*2^n)
    (h : ResetChain n K j m F D)
    (hbig : budget n j*(n+2)<2^n)
    (hlog : 2^(n-m)<n) : False := by
  have hfac : 1≤n+2 := by omega
  have hbudgetLt : budget n j<2^n := by
    have hh := Nat.mul_le_mul_left (budget n j) hfac
    have hle : budget n j≤budget n j*(n+2) := by
      simpa only [Nat.mul_one] using hh
    omega
  obtain ⟨N,C,hN,hbound,hC,hdef,hbalance,hbudget⟩ :=
    h.invariant hn hK hbudgetLt
  have hm : m<n := by
    by_cases hcase : m<n
    · exact hcase
    have hnm : n≤m := by omega
    have hp : 2^n≤2^m := Nat.pow_le_pow_right (by decide) hnm
    omega
  have heq : 2^n=2^m*2^(n-m) := by
    calc
      _=2^(m+(n-m)) := congrArg (fun z:Nat=>2^z) (by omega)
      _=2^m*2^(n-m) := Nat.pow_add 2 m (n-m)
  have hp : 2^m*2^(n-m)<2^m*n :=
    Nat.mul_lt_mul_of_pos_left hlog (Nat.pow_pos (by decide))
  have hp2 : 2^m*n≤budget n j*n :=
    Nat.mul_le_mul_right n hbudget
  have hp3 : budget n j*n≤budget n j*(n+2) :=
    Nat.mul_le_mul_left (budget n j) (by omega)
  omega

#print axioms BB6.Agent50TwoReset.ResetChain.invariant
#print axioms BB6.Agent50TwoReset.ResetChain.excludes_log_wall
end BB6.Agent50TwoReset
