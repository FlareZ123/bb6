import Std

/-!
An abstract 3-to-8 affine return language. The physical D-family return rules
have the form (3*k+r,s) -> (8*k+c,t), with r in {2,3,4}, and
(c,t) determined solely by r and the finite right suffix s.
Theorems below are independent of external source imports: their application
to the original D machine requires the source-to-language bridge.
-/
namespace BB6.Agent39

structure Config where
  n : Nat
  suffix : Nat
  deriving DecidableEq, Repr

def AffineStep (rule : Nat → Nat → Option (Nat × Nat))
    (x y : Config) : Prop :=
  ∃ r k c, (r = 2 ∨ r = 3 ∨ r = 4) ∧
    x.n = 3*k+r ∧ rule r x.suffix = some (c,y.suffix) ∧
    y.n = 8*k+c

inductive AffineSteps (rule : Nat → Nat → Option (Nat × Nat)) :
    Nat → Config → Config → Prop where
  | zero (x) : AffineSteps rule 0 x x
  | succ {n x y z} : AffineStep rule x y → AffineSteps rule n y z →
      AffineSteps rule (n+1) x z

theorem shift_one (rule : Nat → Nat → Option (Nat × Nat))
    {x y : Config} (h : AffineStep rule x y) (d : Nat) :
    AffineStep rule ⟨x.n+3*d, x.suffix⟩ ⟨y.n+8*d,y.suffix⟩ := by
  rcases h with ⟨r,k,c,hr,hn,hb,hy⟩
  refine ⟨r,k+d,c,hr,?_,hb,?_⟩
  · change x.n + 3*d = 3*(k+d)+r
    omega
  · change y.n + 8*d = 8*(k+d)+c
    omega

theorem shadow (rule : Nat → Nat → Option (Nat × Nat))
    {n : Nat} {x y : Config} (h : AffineSteps rule n x y) (d : Nat) :
    ∃ z, AffineSteps rule n ⟨x.n+3^n*d,x.suffix⟩ z ∧
         z.suffix = y.suffix ∧ z.n = y.n+8^n*d := by
  induction h generalizing d with
  | zero x =>
      refine ⟨⟨x.n+3^0*d,x.suffix⟩, ?_, rfl, ?_⟩
      · exact AffineSteps.zero _
      · simp
  | @succ k x y z hfirst hrest ih =>
      obtain ⟨z',hsecond,hs,hn⟩ := ih (8*d)
      have hfirst' : AffineStep rule
          ⟨x.n+3^(k+1)*d,x.suffix⟩
          ⟨y.n+3^k*(8*d),y.suffix⟩ := by
        simpa only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
          (shift_one rule hfirst (3^k*d))
      refine ⟨z', AffineSteps.succ hfirst' hsecond, hs, ?_⟩
      simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hn

inductive DifferenceChain : Nat → Nat → Nat → Prop where
  | zero (d) : DifferenceChain 0 d d
  | succ {k d e f} : 3*e = 8*d → DifferenceChain k e f →
      DifferenceChain (k+1) d f

private theorem coprime_three_power_eight (n : Nat) :
    (3^n).Coprime 8 := (show (3 : Nat).Coprime 8 from by decide).pow_left n

theorem difference_divisible {k d e : Nat} (h : DifferenceChain k d e) :
    3^k ∣ d := by
  induction h with
  | zero d => simp
  | @succ k d e f heq hrest ih =>
      rcases ih with ⟨w,hw⟩
      have hm : 3^(k+1) ∣ 8*d := by
        refine ⟨w, ?_⟩
        calc
          8*d = 3*e := heq.symm
          _ = 3*(3^k*w) := by rw [hw]
          _ = 3^(k+1)*w := by simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
      exact (coprime_three_power_eight (k+1)).dvd_of_dvd_mul_left hm

theorem nat_lt_three_pow (k : Nat) : k < 3^k := by
  induction k with
  | zero => decide
  | succ k ih =>
      rw [Nat.pow_succ]
      omega

theorem no_perpetual_positive_difference (d : Nat) (hd : 0 < d)
    (h : ∀ k, ∃ e, DifferenceChain k d e) : False := by
  obtain ⟨e,he⟩ := h (d+1)
  have hv := difference_divisible he
  rcases hv with ⟨w,hw⟩
  have hp : d+1 < 3^(d+1) := nat_lt_three_pow (d+1)
  have hwpos : 0<w := by
    cases w with
    | zero => simp at hw; omega
    | succ v => omega
  have hprod : 3^(d+1) ≤ 3^(d+1)*w := by
    exact Nat.le_mul_of_pos_right (3^(d+1)) hwpos
  omega

/-!
The primitive-step time of each authenticated conditional D return has a
quadratic dependence on the section quotient k, with +24*k per consumed 111
token in an A-code. This lemma gives the exact time-shift polynomial.
-/
def ReturnCost (k tripleCount fixedCost : Nat) : Nat :=
  12*k*k + (49+24*tripleCount)*k + fixedCost

theorem return_cost_shift (k d tripleCount fixedCost : Nat) :
    ReturnCost (k+d) tripleCount fixedCost =
      ReturnCost k tripleCount fixedCost +
        24*k*d + 12*d*d + (49+24*tripleCount)*d := by
  simp only [ReturnCost, Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
  rw [Nat.mul_comm d k]
  omega

/-!
Matching two finite trajectories means each return consumes the same source
residue r and suffix code, uses the same constant c, and produces the same
suffix. The resulting unary difference must undergo 3*next = 8*previous.
-/
def MatchedStep (rule : Nat → Nat → Option (Nat × Nat))
    (x x' y y' : Config) : Prop :=
  ∃ r k l c t, (r = 2 ∨ r = 3 ∨ r = 4) ∧
    x.n = 3*k+r ∧ x'.n = 3*l+r ∧ k ≤ l ∧
    x.suffix = x'.suffix ∧ rule r x.suffix = some (c,t) ∧
    y.n = 8*k+c ∧ y'.n = 8*l+c ∧
    y.suffix = t ∧ y'.suffix = t

theorem matched_difference (rule : Nat → Nat → Option (Nat × Nat))
    {x x' y y' : Config} (h : MatchedStep rule x x' y y') :
    3*(y'.n-y.n) = 8*(x'.n-x.n) := by
  rcases h with ⟨r,k,l,c,t,hr,hx,hx',hkl,hs,hb,hy,hy',ht,ht'⟩
  omega

inductive MatchedSteps (rule : Nat → Nat → Option (Nat × Nat)) :
    Nat → Config → Config → Config → Config → Prop where
  | zero (x x') : MatchedSteps rule 0 x x' x x'
  | succ {k x x' y y' z z'} :
      MatchedStep rule x x' y y' →
      MatchedSteps rule k y y' z z' →
      MatchedSteps rule (k+1) x x' z z'

theorem matched_differences_form_chain
    (rule : Nat → Nat → Option (Nat × Nat))
    {k : Nat} {x x' z z' : Config}
    (h : MatchedSteps rule k x x' z z') :
    DifferenceChain k (x'.n-x.n) (z'.n-z.n) := by
  induction h with
  | zero x x' => exact DifferenceChain.zero _
  | succ hfirst hrest ih =>
      exact DifferenceChain.succ (matched_difference rule hfirst) ih

theorem no_distinct_perpetual_matched_orbits
    (rule : Nat → Nat → Option (Nat × Nat))
    (x x' : Config) (hsep : x.n < x'.n)
    (hsync : ∀ k, ∃ z z', MatchedSteps rule k x x' z z') : False := by
  apply no_perpetual_positive_difference (x'.n-x.n) (by omega)
  intro k
  obtain ⟨z,z',h⟩ := hsync k
  exact ⟨z'.n-z.n, matched_differences_form_chain rule h⟩

#print axioms shift_one
#print axioms shadow
#print axioms difference_divisible
#print axioms no_perpetual_positive_difference
#print axioms return_cost_shift
#print axioms matched_difference
#print axioms matched_differences_form_chain
#print axioms no_distinct_perpetual_matched_orbits
end BB6.Agent39
