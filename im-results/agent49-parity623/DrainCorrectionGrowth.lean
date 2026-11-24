import Std.Tactic

/-! Arithmetic model of the positive-budget branches of the #623 flat drain.
The source branch identities are `drain_three`, `drain_three_one`, and
`drain_three_two` in Agent49FlatDrainSource.  The model does not assert an
original-machine outcome or formalize the real-asymptotic obstruction. -/
namespace BB6.Agent49CorrectionGrowth

inductive PositiveTrace : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Prop
  | stop (a z : Nat) : PositiveTrace a 0 z a z 0 0 0
  | r0 {a q z aa dd n0 n1 n2 : Nat} (hq : 0 < q) (ha : 0 < a)
      (h : PositiveTrace (a+1) (q-1) (z+6*q+3) aa dd n0 n1 n2) :
      PositiveTrace a (3*q) z aa dd (n0+1) n1 n2
  | r1 {a q z aa dd n0 n1 n2 : Nat} (ha : 0 < a)
      (h : PositiveTrace (a-1) q (z+6*q+7) aa dd n0 n1 n2) :
      PositiveTrace a (3*q+1) z aa dd n0 (n1+1) n2
  | r2 {a q z aa dd n0 n1 n2 : Nat} (ha : 0 < a)
      (h : PositiveTrace (a-1) (q+1) (z+6*q+5) aa dd n0 n1 n2) :
      PositiveTrace a (3*q+2) z aa dd n0 n1 (n2+1)

theorem counts {a b z aa dd n0 n1 n2 : Nat}
    (h : PositiveTrace a b z aa dd n0 n1 n2) :
    aa+n1+n2 = a+n0 ∧ dd=z+3*b+4*n1+2*n2 := by
  induction h with
  | stop => omega
  | r0 hq ha _ ih => omega
  | r1 ha _ ih => omega
  | r2 ha _ ih => omega

theorem length_lower {a b z aa dd n0 n1 n2 : Nat}
    (h : PositiveTrace a b z aa dd n0 n1 n2) :
    2*b+3 ≤ 3^(n0+n1+n2+1) := by
  induction h with
  | stop => simp
  | @r0 a q z aa dd n0 n1 n2 hq ha _ ih =>
    have he : n0+1+n1+n2+1 = (n0+n1+n2+1)+1 := by omega
    rw [he, Nat.pow_succ]
    omega
  | @r1 a q z aa dd n0 n1 n2 ha _ ih =>
    have he : n0+(n1+1)+n2+1 = (n0+n1+n2+1)+1 := by omega
    rw [he, Nat.pow_succ]
    omega
  | @r2 a q z aa dd n0 n1 n2 ha _ ih =>
    have he : n0+n1+(n2+1)+1 = (n0+n1+n2+1)+1 := by omega
    rw [he, Nat.pow_succ]
    omega

theorem length_le_error {a b z aa dd n0 n1 n2 : Nat}
    (h : PositiveTrace a b z aa dd n0 n1 n2) :
    n0+n1+n2 ≤ (aa-a)+(dd-(z+3*b)) := by
  obtain ⟨hfirst, hthird⟩ := counts h
  omega

/-- The input block length is exponentially bounded by a *one-sided*
first-coordinate increase plus third-coordinate excess, rather than an
absolute first-coordinate error. -/
theorem correction_growth {a b z aa dd n0 n1 n2 : Nat}
    (h : PositiveTrace a b z aa dd n0 n1 n2) :
    2*b+3 ≤ 3^((aa-a)+(dd-(z+3*b))+1) := by
  have hh := length_lower h
  have he := length_le_error h
  exact Nat.le_trans hh (Nat.pow_le_pow_right (by decide : 0 < 3) (by omega))

/-- Transfer to any evaluator with the exact four positive-budget equations.
A binary length budget bounds the number of flat steps and guarantees that
all nonterminal first counters are positive. No evaluator implementation is
assumed beyond the displayed equations. -/
theorem positive_trace_exists {σ : Type} (B : Nat → Nat → Nat → Option σ)
    (D : Nat → Nat → σ)
    (hz : ∀ a z, B a 0 z = some (D a z))
    (h0 : ∀ a q z, 0 < q → B a (3*q) z = B (a+1) (q-1) (z+6*q+3))
    (h1 : ∀ a q z, 0 < a → B a (3*q+1) z = B (a-1) q (z+6*q+7))
    (h2 : ∀ a q z, 0 < a → B a (3*q+2) z = B (a-1) (q+1) (z+6*q+5))
    (n a b z : Nat) (ha : n ≤ a) (hb : b < 2^n) :
    ∃ aa dd n0 n1 n2, B a b z = some (D aa dd) ∧
      PositiveTrace a b z aa dd n0 n1 n2 := by
  induction n generalizing a b z with
  | zero =>
    simp at hb
    subst b
    exact ⟨a,z,0,0,0,hz a z,PositiveTrace.stop a z⟩
  | succ n ih =>
    by_cases hb0 : b=0
    · subst b
      exact ⟨a,z,0,0,0,hz a z,PositiveTrace.stop a z⟩
    · have ha0 : 0<a := by omega
      have hp : 2^(n+1)=2*2^n := by rw [Nat.pow_succ]; omega
      have hp1 : 0<2^n := Nat.pow_pos (by decide)
      let q := b/3
      have hrep : b=3*q+b%3 := by dsimp [q]; omega
      by_cases hr0 : b%3=0
      · have hq : 0<q := by omega
        have hq' : q-1<2^n := by omega
        obtain ⟨aa,dd,n0,n1,n2,he,ht⟩ := ih (a+1) (q-1) (z+6*q+3) (by omega) hq'
        have hrep0 : b=3*q := by omega
        rw [hrep0, h0 a q z hq, he]
        exact ⟨aa,dd,n0+1,n1,n2,rfl,PositiveTrace.r0 hq ha0 ht⟩
      · by_cases hr1 : b%3=1
        · have hq' : q<2^n := by omega
          obtain ⟨aa,dd,n0,n1,n2,he,ht⟩ := ih (a-1) q (z+6*q+7) (by omega) hq'
          have hrep1 : b=3*q+1 := by omega
          rw [hrep1, h1 a q z ha0, he]
          exact ⟨aa,dd,n0,n1+1,n2,rfl,PositiveTrace.r1 ha0 ht⟩
        · have hq' : q+1<2^n := by omega
          obtain ⟨aa,dd,n0,n1,n2,he,ht⟩ := ih (a-1) (q+1) (z+6*q+5) (by omega) hq'
          have hrep2 : b=3*q+2 := by omega
          rw [hrep2, h2 a q z ha0, he]
          exact ⟨aa,dd,n0,n1,n2+1,rfl,PositiveTrace.r2 ha0 ht⟩

/-- Uniform inverse window, including visits to the zero first counter.
Every equation is a hypothesis so the result can be applied to the unchanged
source drain without introducing a second semantic implementation. -/
theorem successful_window {σ : Type} (B : Nat → Nat → Nat → Option σ)
    (D : Nat → Nat → σ)
    (hinj : ∀ a z x y, D a z = D x y → a=x ∧ z=y)
    (hz : ∀ a z, B a 0 z = some (D a z))
    (h0 : ∀ a q z, 0 < q → B a (3*q) z = B (a+1) (q-1) (z+6*q+3))
    (h1 : ∀ a q z, 0 < a → B a (3*q+1) z = B (a-1) q (z+6*q+7))
    (h10 : ∀ q z, B 0 (3*q+1) z = none)
    (h2 : ∀ a q z, 0 < a → B a (3*q+2) z = B (a-1) (q+1) (z+6*q+5))
    (h20 : ∀ q z, B 0 (3*q+2) z = B 0 q (z+6*q+7))
    (n a b z x y : Nat) (hb : b < 2^n) (hs : B a b z=some (D x y)) :
    a≤x+n ∧ x≤a+n ∧ z+3*b≤y ∧ y≤z+3*b+4*n := by
  induction n generalizing a b z with
  | zero =>
    simp at hb
    subst b
    rw [hz] at hs
    have hh := hinj a z x y (Option.some.inj hs)
    omega
  | succ n ih =>
    by_cases hb0 : b=0
    · subst b
      rw [hz] at hs
      have hh := hinj a z x y (Option.some.inj hs)
      omega
    · have hp : 2^(n+1)=2*2^n := by rw [Nat.pow_succ]; omega
      have hp1 : 0<2^n := Nat.pow_pos (by decide)
      let q := b/3
      have hrep : b=3*q+b%3 := by dsimp [q]; omega
      by_cases hr0 : b%3=0
      · have hq : 0<q := by omega
        have hq' : q-1<2^n := by omega
        have hrep0 : b=3*q := by omega
        rw [hrep0,h0 a q z hq] at hs
        have hh := ih (a+1) (q-1) (z+6*q+3) hq' hs
        omega
      · by_cases hr1 : b%3=1
        · have hq' : q<2^n := by omega
          have hrep1 : b=3*q+1 := by omega
          by_cases ha : a=0
          · subst a
            rw [hrep1,h10] at hs
            contradiction
          · rw [hrep1,h1 a q z (by omega)] at hs
            have hh := ih (a-1) q (z+6*q+7) hq' hs
            omega
        · have hrep2 : b=3*q+2 := by omega
          by_cases ha : a=0
          · subst a
            have hq' : q<2^n := by omega
            rw [hrep2,h20] at hs
            have hh := ih 0 q (z+6*q+7) hq' hs
            omega
          · have hq' : q+1<2^n := by omega
            rw [hrep2,h2 a q z (by omega)] at hs
            have hh := ih (a-1) (q+1) (z+6*q+5) hq' hs
            omega

/-- The same inverse window with an explicit budget computed solely from
output y: n=1+floor(log2(y)). This is an all-natural statement. -/
theorem inverse_window {σ : Type} (B : Nat → Nat → Nat → Option σ)
    (D : Nat → Nat → σ)
    (hinj : ∀ a z x y, D a z = D x y → a=x ∧ z=y)
    (hz : ∀ a z, B a 0 z = some (D a z))
    (h0 : ∀ a q z, 0 < q → B a (3*q) z = B (a+1) (q-1) (z+6*q+3))
    (h1 : ∀ a q z, 0 < a → B a (3*q+1) z = B (a-1) q (z+6*q+7))
    (h10 : ∀ q z, B 0 (3*q+1) z = none)
    (h2 : ∀ a q z, 0 < a → B a (3*q+2) z = B (a-1) (q+1) (z+6*q+5))
    (h20 : ∀ q z, B 0 (3*q+2) z = B 0 q (z+6*q+7))
    (a b z x y : Nat) (hs : B a b z=some (D x y)) :
    let n := y.log2+1
    a≤x+n ∧ x≤a+n ∧ z+3*b≤y ∧ y≤z+3*b+4*n := by
  have hu := successful_window B D hinj hz h0 h1 h10 h2 h20 b a b z x y
    Nat.lt_two_pow_self hs
  have hy : y<2^(y.log2+1) := by
    by_cases hy0 : y=0
    · subst y; decide
    · exact (Nat.log2_lt hy0).mp (by omega)
  have hb : b<2^(y.log2+1) := by omega
  exact successful_window B D hinj hz h0 h1 h10 h2 h20 _ a b z x y hb hs

/-- Excess over 3*b in the positive-budget third-coordinate output. -/
def excess (b : Nat) : Nat :=
  if b=0 then 0
  else if b%3=0 then excess (b/3-1)
  else if b%3=1 then 4+excess (b/3)
  else 2+excess (b/3+1)
termination_by b
decreasing_by
  all_goals omega

theorem excess_zero : excess 0 = 0 := by rw [excess]; simp

theorem excess_three (q : Nat) (hq : 0<q) :
    excess (3*q)=excess (q-1) := by
  conv => lhs; rw [excess]
  have hn : 3*q ≠ 0 := by omega
  have hm : (3*q)%3=0 := by omega
  have hd : (3*q)/3=q := by omega
  simp [hn,hm,hd]

theorem excess_one (q : Nat) : excess (3*q+1)=4+excess q := by
  conv => lhs; rw [excess]
  have hn : 3*q+1 ≠ 0 := by omega
  have hm : (3*q+1)%3=1 := by omega
  have hd : (3*q+1)/3=q := by omega
  simp [hn,hm,hd]

theorem excess_two (q : Nat) : excess (3*q+2)=2+excess (q+1) := by
  conv => lhs; rw [excess]
  have hn : 3*q+2 ≠ 0 := by omega
  have hm : (3*q+2)%3=2 := by omega
  have hd : (3*q+2)/3=q := by omega
  simp [hn,hm,hd]

theorem trace_excess {a b z aa dd n0 n1 n2 : Nat}
    (h : PositiveTrace a b z aa dd n0 n1 n2) :
    excess b = 4*n1+2*n2 := by
  induction h with
  | stop => simp [excess_zero]
  | r0 hq ha _ ih => rw [excess_three _ hq]; exact ih
  | r1 ha _ ih => rw [excess_one,ih]; omega
  | r2 ha _ ih => rw [excess_two,ih]; omega

def image (b : Nat) : Nat := 3*b+excess b

theorem trace_image {a b z aa dd n0 n1 n2 : Nat}
    (h : PositiveTrace a b z aa dd n0 n1 n2) : dd=z+image b := by
  have he := trace_excess h
  have hc := (counts h).2
  simp [image,he]
  omega

/-- Signed first-counter change for a positive-budget drain. -/
def drift (b : Nat) : Int :=
  if b=0 then 0
  else if b%3=0 then 1+drift (b/3-1)
  else if b%3=1 then drift (b/3)-1
  else drift (b/3+1)-1
termination_by b
decreasing_by
  all_goals omega

theorem trace_drift {a b z aa dd n0 n1 n2 : Nat}
    (h : PositiveTrace a b z aa dd n0 n1 n2) :
    (aa : Int) = (a : Int)+drift b := by
  induction h with
  | stop => rw [drift]; simp
  | @r0 a q z aa dd n0 n1 n2 hq ha _ ih =>
    have hh : drift (3*q)=1+drift (q-1) := by
      conv => lhs; rw [drift]
      simp [show 3*q≠0 by omega, show (3*q)%3=0 by omega, show (3*q)/3=q by omega]
    rw [hh]; omega
  | @r1 a q z aa dd n0 n1 n2 ha _ ih =>
    have hh : drift (3*q+1)=drift q-1 := by
      conv => lhs; rw [drift]
      simp [show 3*q+1≠0 by omega, show (3*q+1)%3=1 by omega, show (3*q+1)/3=q by omega]
    rw [hh]; omega
  | @r2 a q z aa dd n0 n1 n2 ha _ ih =>
    have hh : drift (3*q+2)=drift (q+1)-1 := by
      conv => lhs; rw [drift]
      simp [show 3*q+2≠0 by omega, show (3*q+2)%3=2 by omega, show (3*q+2)/3=q by omega]
    rw [hh]; omega

/-- Adding two input blocks cannot decrease the excess by more than four,
even across arbitrarily long ternary carries. -/
theorem excess_step_two (b : Nat) : excess b ≤ excess (b+2)+4 := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    by_cases hb : b=0
    · subst b
      rw [excess_zero]; omega
    · let q := b/3
      have hdiv : b=3*q+b%3 := by dsimp [q]; omega
      by_cases hr0 : b%3=0
      · have hq : 0<q := by omega
        have he : b=3*q := by omega
        have he2 : b+2=3*q+2 := by omega
        have hq2 : q-1+2=q+1 := by omega
        have hh := ih (q-1) (by omega)
        rw [hq2] at hh
        rw [he2, he, excess_three _ hq, excess_two]
        omega
      · by_cases hr1 : b%3=1
        · have he : b=3*q+1 := by omega
          have he2 : b+2=3*(q+1) := by omega
          rw [he2, he, excess_one, excess_three _ (by omega)]
          simp
          omega
        · have he : b=3*q+2 := by omega
          have he2 : b+2=3*(q+1)+1 := by omega
          rw [he2, he, excess_two, excess_one]
          omega

/-- Strictly increasing, with slope at least one, within either parity. -/
theorem image_step_two (b : Nat) : image b+2 ≤ image (b+2) := by
  have h := excess_step_two b
  unfold image
  omega

theorem image_progression (b k : Nat) : image b+2*k ≤ image (b+2*k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := image_step_two (b+2*k)
    have he : b+2*(k+1)=b+2*k+2 := by omega
    rw [he]
    omega

theorem excess_even (b : Nat) : excess b % 2=0 := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    by_cases hb : b=0
    · subst b; rw [excess_zero]
    · let q := b/3
      have hdiv : b=3*q+b%3 := by dsimp [q]; omega
      by_cases hr0 : b%3=0
      · have hq : 0<q := by omega
        have he : b=3*q := by omega
        rw [he,excess_three _ hq]
        exact ih (q-1) (by omega)
      · by_cases hr1 : b%3=1
        · have he : b=3*q+1 := by omega
          rw [he,excess_one]
          have hh := ih q (by omega)
          omega
        · have he : b=3*q+2 := by omega
          rw [he,excess_two]
          have hh := ih (q+1) (by omega)
          omega

theorem image_parity (b : Nat) : image b%2=b%2 := by
  have h := excess_even b
  unfold image
  omega

/-- The full positive-budget third-coordinate image is injective on Nat,
even though it is not monotonically increasing across parity classes. -/
theorem image_injective : Function.Injective image := by
  intro b c he
  have hb := image_parity b
  have hc := image_parity c
  by_cases h : b<c
  · have hd : c=b+2*((c-b)/2) := by omega
    have hh := image_progression b ((c-b)/2)
    rw [←hd,he] at hh
    omega
  · by_cases h' : c<b
    · have hd : b=c+2*((b-c)/2) := by omega
      have hh := image_progression c ((b-c)/2)
      rw [←hd,he] at hh
      omega
    · omega

#print axioms counts
#print axioms length_lower
#print axioms length_le_error
#print axioms correction_growth
#print axioms positive_trace_exists
#print axioms successful_window
#print axioms inverse_window
#print axioms trace_image
#print axioms trace_drift
#print axioms excess_step_two
#print axioms image_step_two
#print axioms image_injective
end BB6.Agent49CorrectionGrowth
