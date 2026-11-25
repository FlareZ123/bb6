import Std.Tactic

namespace BB6.Agent49InverseOrder

/-- Positive-budget section statistics. These laws are instantiated by the
existing source-linked `excess` and `drift` functions. -/
structure Laws (E : Nat → Nat) (J : Nat → Int) : Prop where
  ez : E 0 = 0
  e0 : ∀ q, 0 < q → E (3*q) = E (q-1)
  e1 : ∀ q, E (3*q+1) = 4+E q
  e2 : ∀ q, E (3*q+2) = 2+E (q+1)
  jz : J 0 = 0
  j0 : ∀ q, 0 < q → J (3*q) = 1+J (q-1)
  j1 : ∀ q, J (3*q+1) = J q-1
  j2 : ∀ q, J (3*q+2) = J (q+1)-1

def F (E : Nat → Nat) (b : Nat) : Int := 3*(b : Int)+(E b : Int)
def H (E : Nat → Nat) (J : Nat → Int) (b : Nat) : Int := F E b+J b
def G (J : Nat → Int) (b : Nat) : Int := (b : Int)-J b

/-- The compensated image has only three possible adjacent same-parity gaps.
The first-coordinate drift cannot increase by more than two on such a step. -/
theorem adjacent {E J} (h : Laws E J) (b : Nat) :
    (H E J (b+2)-H E J b = 4 ∨ H E J (b+2)-H E J b = 8 ∨
      H E J (b+2)-H E J b = 10) ∧
    J (b+2) ≤ J b+2 ∧
    (b%3=2 → H E J (b+2)-H E J b = 8) := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    by_cases hz : b=0
    · subst b
      have he1 := h.e1 0
      have he2 := h.e2 0
      have hj1 := h.j1 0
      have hj2 := h.j2 0
      change E 1 = 4 + E 0 at he1
      change E 2 = 2 + E 1 at he2
      change J 1 = J 0 - 1 at hj1
      change J 2 = J 1 - 1 at hj2
      rw [h.ez] at he1
      rw [h.jz] at hj1
      change (H E J 2-H E J 0=4 ∨ H E J 2-H E J 0=8 ∨ H E J 2-H E J 0=10) ∧ J 2 ≤ J 0+2 ∧ (0%3=2 → H E J 2-H E J 0=8)
      simp only [H,F,h.ez,h.jz]
      omega
    · let q := b/3
      have hb : b=3*q+b%3 := by dsimp [q]; omega
      by_cases hr0 : b%3=0
      · have hq : 0<q := by omega
        have hq2 : q-1+2=q+1 := by omega
        have hc := ih (q-1) (by omega)
        rw [hq2] at hc
        have h0 : b=3*q := by omega
        have h2 : b+2=3*q+2 := by omega
        rw [h0] at hr0
        rw [h2,h0]
        simp only [H,F,h.e0 q hq,h.e2,h.j0 q hq,h.j2] at *
        obtain ⟨hh,hj,_⟩ := hc
        refine ⟨?_,?_,by omega⟩
        · rcases hh with hh|hh|hh <;> omega
        · omega
      · by_cases hr1 : b%3=1
        · have h1 : b=3*q+1 := by omega
          have h3 : b+2=3*(q+1) := by omega
          rw [h3,h1]
          simp only [H,F,h.e1,h.e0 (q+1) (by omega),h.j1,h.j0 (q+1) (by omega)]
          have hq' : q+1-1=q := by omega
          rw [hq']
          omega
        · have h2 : b=3*q+2 := by omega
          have h4 : b+2=3*(q+1)+1 := by omega
          rw [h4,h2]
          simp only [H,F,h.e2,h.e1,h.j2,h.j1]
          omega

/-- Pairwise increase and upper slope for the inverse's large coordinate. -/
theorem progression {E J} (h : Laws E J) (b k : Nat) :
    4*(k : Int) ≤ H E J (b+2*k)-H E J b ∧
    H E J (b+2*k)-H E J b ≤ 10*(k : Int) ∧
    G J b ≤ G J (b+2*k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := adjacent h (b+2*k)
    have he : b+2*(k+1)=b+2*k+2 := by omega
    rw [he]
    obtain ⟨ha,hj,_⟩ := hh
    obtain ⟨hl,hu,hg⟩ := ih
    simp only [G] at hg ⊢
    rcases ha with ha|ha|ha <;> omega

/-- Every three parity steps contain a residue-two step, giving at least
four additional units of compensated-image growth. -/
theorem triple {E J} (h : Laws E J) (b : Nat) :
    H E J b+16 ≤ H E J (b+6) := by
  have h0 := adjacent h b
  have h1 := adjacent h (b+2)
  have h2 := adjacent h (b+4)
  have h1' : b+2+2=b+4 := by omega
  have h2' : b+4+2=b+6 := by omega
  rw [h1'] at h1
  rw [h2'] at h2
  have hg (x : Nat) (hh : H E J (x+2)-H E J x=4 ∨
      H E J (x+2)-H E J x=8 ∨ H E J (x+2)-H E J x=10) :
      H E J x+4 ≤ H E J (x+2) := by rcases hh with h|h|h <;> omega
  have a := hg b h0.1
  have c := progression h (b+2) 1
  have d := progression h (b+4) 1
  simp only [Nat.mul_one] at c d
  rw [h1'] at c
  rw [h2'] at d
  have hr : b%3=0 ∨ b%3=1 ∨ b%3=2 := by omega
  rcases hr with hr|hr|hr
  · have t := h1.2.2 (by omega); omega
  · have t := h2.2.2 (by omega); omega
  · have t := h0.2.2 hr; omega

theorem triple_progression {E J} (h : Laws E J) (b k : Nat) :
    H E J b+16*(k : Int) ≤ H E J (b+6*k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hh := triple h (b+6*k)
    rw [show b+6*(k+1)=b+6*k+6 by omega]
    omega

/-- The ordered inverse branch contracts the L1 width of a target family.
Here `x` is the output first counter and `b` the decoded drain budget. The
parent coordinates, up to branch-dependent constants and exchange, are
`x + G(b)` and `b`; the output third coordinate is `F(b)+z`.
This statement quantifies over every ordered pair, not a finite scan. -/
theorem inverse_width {E J} (h : Laws E J) (x x' : Int) (hx : x ≤ x')
    (b k : Nat) :
    x+G J b ≤ x'+G J (b+2*k) ∧
    x'+G J (b+2*k)+(b+2*k : Nat) - (x+G J b+b) +
      4*((k/3 : Nat) : Int) ≤ x'+F E (b+2*k) - (x+F E b) := by
  have hmono := progression h b k
  have htrip := triple_progression h b (k/3)
  have hrest := progression h (b+6*(k/3)) (k%3)
  have he : b+6*(k/3)+2*(k%3)=b+2*k := by omega
  rw [he] at hrest
  simp only [H,G] at *
  omega

#print axioms adjacent
#print axioms progression
#print axioms triple_progression
#print axioms inverse_width
end BB6.Agent49InverseOrder
