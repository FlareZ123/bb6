import ReturnSource

namespace BB6.Agent9ReturnGCD
open BB6.Agent45.DelayedCarry

/-- Divide out the entire power-of-two slope before the confinement phase.
    This recovers the r bits otherwise lost from the initial magnitude. -/
theorem scale_slope (g : Int) (h L r A : Nat) (a x : Nat→Int)
    (hg : g=(2:Int)^r*(h:Int))
    (hs : ∀ j<L, 2*a (j+1)=a j+g*x j)
    (hr : r≤L)
    (hinit : -(2:Int)^(A+r)<a 0 ∧ a 0<g+(2:Int)^(A+r)) :
    ∃ b : Nat→Int,
      (∀ j≤L-r, (2:Int)^r*b j=a j) ∧
      (∀ j<L-r, 2*b (j+1)=b j+(h:Int)*x j) ∧
      (-(2:Int)^A<b 0 ∧ b 0<(h:Int)+(2:Int)^A) := by
  let P : Int := 2^r
  have hP : 0<P := Int.pow_pos (by decide)
  let b : Nat→Int := fun j => a j/P
  have hm : ∀ j≤L-r, P*b j=a j := by
    intro j hj
    have hd : P ∣ a j := slope_divisible g a x L r (h:Int) hg hs j (by omega)
    dsimp [b]
    rw [Int.mul_comm]
    exact Int.ediv_mul_cancel hd
  refine ⟨b,hm,?_,?_⟩
  · intro j hj
    have hh := hs j (by omega)
    rw [←hm j (by omega),←hm (j+1) (by omega),hg] at hh
    change 2*(P*b (j+1))=P*b j+(P*(h:Int))*x j at hh
    apply Int.eq_of_mul_eq_mul_left (show P≠0 by omega)
    rw [Int.mul_add]
    simpa only [show P*(2*b (j+1))=2*(P*b (j+1)) by ac_rfl,Int.mul_assoc] using hh
  · have he : (2:Int)^(A+r)=P*(2:Int)^A := by rw [Int.pow_add]; dsimp [P]; ac_rfl
    rw [he,←hm 0 (by omega),hg,←Int.mul_neg,←Int.mul_add] at hinit
    change P*(-(2:Int)^A)<P*b 0 ∧ P*b 0<P*((h:Int)+(2:Int)^A) at hinit
    constructor
    · by_cases hh : -(2:Int)^A<b 0
      · exact hh
      · have hh' := Int.mul_le_mul_of_nonneg_left (show b 0≤ -(2:Int)^A by omega) (by omega : 0≤P)
        exact False.elim (by omega)
    · by_cases hh : b 0<(h:Int)+(2:Int)^A
      · exact hh
      · have hh' := Int.mul_le_mul_of_nonneg_left (show (h:Int)+(2:Int)^A≤b 0 by omega) (by omega : 0≤P)
        exact False.elim (by omega)

/-- The improved general slope bound. A+r now occurs inside the initial
    exponential magnitude, not merely A. -/
theorem no_small_slope_scaled (q dir C g : Int) (h L A r B : Nat)
    (a c w x : Nat→Int)
    (hdir : dir=1∨dir= -1) (hodd : h%2=1)
    (hg : g=(2:Int)^r*(h:Int)) (hL : A+r+2*h+B≤L)
    (hinit : -(2:Int)^(A+r)<a 0 ∧ a 0<g+(2:Int)^(A+r))
    (hx : ∀ j<L, x j=0∨x j=1)
    (hs : ∀ j<L, 2*c (j+1)=c j+(q+dir*(j:Int))*x j)
    (hw : ∀ j<L, x j=1 → 2*w (j+1)=w j)
    (ha : ∀ j<L, 2*a (j+1)=a j+g*x j)
    (hbound : ∀ j≤L, 1≤c j ∧ c j≤C ∧ 1≤w j ∧ w j≤C)
    (hscale : (h:Int)*(C+(h:Int))<(2:Int)^B) : False := by
  obtain ⟨b,hm,hb,hinit'⟩ := scale_slope g h L r A a x hg ha (by omega) hinit
  have hconf := slope_confined (h:Int) b x A (by omega)
    (fun j hj => hx j (by omega)) (fun j hj => hb j (by omega)) hinit'
  apply no_small_odd_slope (q+dir*(A:Int)) dir C h (L-r-A) B
    (fun j => b (A+j)) (fun j => c (A+j)) (fun j => w (A+j)) (fun j => x (A+j))
    hdir hodd (by omega)
  · simpa using hconf
  · intro j hj; exact hx (A+j) (by omega)
  · intro j hj
    have hh := hs (A+j) (by omega)
    simp only [Int.natCast_add,Int.mul_add] at hh
    simpa only [Nat.add_assoc,Int.add_assoc] using hh
  · intro j hj h1
    simpa only [Nat.add_assoc] using hw (A+j) (by omega) h1
  · intro j hj
    simpa only [Nat.add_assoc] using hb (A+j) (by omega)
  · intro j hj; exact hbound (A+j) (by omega)
  · exact hscale

/-- A power-of-two shift alone forces the unit slope, with no 2h overhead.
    Works for arbitrary base clock, not just affine clocks. -/
theorem no_dyadic_paired_return (clock : Nat→Int) (r L A K : Nat) (C : Int)
    (c d w x : Nat→Int)
    (hL : A+r+K≤L)
    (hinit : -(2:Int)^(A+r)<c 0-d 0 ∧ c 0-d 0<(2:Int)^r+(2:Int)^(A+r))
    (hx : ∀ j<L, x j=0∨x j=1)
    (hc : ∀ j<L, 2*c (j+1)=c j+clock j*x j)
    (hd : ∀ j<L, 2*d (j+1)=d j+(clock j-(2:Int)^r)*x j)
    (hw : ∀ j<L, x j=1 → 2*w (j+1)=w j)
    (hbound : ∀ j≤L, 1≤c j ∧ c j≤C ∧ 1≤w j ∧ w j≤C)
    (hscale : C<(2:Int)^K) : False := by
  let a : Nat→Int := fun j => c j-d j
  have hA : ∀ j<L, 2*a (j+1)=a j+(2:Int)^r*x j := by
    intro j hj
    have h1 := hc j hj
    have h2 := hd j hj
    dsimp [a]
    rw [Int.mul_sub]
    rcases hx j hj with h|h <;> rw [h] at h1 h2 ⊢ <;> simp at h1 h2 ⊢ <;> omega
  obtain ⟨b,hm,hb,hinit'⟩ := scale_slope ((2:Int)^r) 1 L r A a x (by simp)
    (fun j hj => by simpa using hA j hj) (by omega) (by simpa [a] using hinit)
  have hconf := slope_confined 1 b x A (by decide)
    (fun j hj => hx j (by omega)) (fun j hj => by simpa using hb j (by omega)) (by simpa using hinit')
  have h0 : b A=0∨b A=1 := by omega
  have hlock := unit_lock b x A K h0 (fun j hj => hx j (by omega)) (fun j hj => by simpa using hb j (by omega))
  rcases h0 with h0|h0
  · apply no_positive_halves (fun j => c (A+j)) K
    · intro j hj
      have hh := hc (A+j) (by omega)
      rw [hlock j hj,h0,Int.mul_zero,Int.add_zero] at hh
      simpa [Nat.add_assoc] using hh
    · exact (hbound (A+K) (by omega)).1
    · exact Int.lt_of_le_of_lt (hbound A (by omega)).2.1 hscale
  · apply no_positive_halves (fun j => w (A+j)) K
    · intro j hj
      simpa only [Nat.add_assoc] using hw (A+j) (by omega) ((hlock j hj).trans h0)
    · exact (hbound (A+K) (by omega)).2.2.1
    · exact Int.lt_of_le_of_lt (hbound A (by omega)).2.2.2 hscale

/-- For every original Trace, no dyadic shift can match 2n+6 selected bits.
    The bound is independent of the dyadic exponent. -/
theorem trace_no_uniform_dyadic_repeat {n m W a : Nat} (hn : 14≤n) (heven : n%2=0)
    (ht : Trace n m W a) (i r : Nat)
    (hp : i+2^r+(2*n+6)≤m)
    (hrep : ∀ j<2*n+6, W.testBit (i+2^r+j)=W.testBit (i+j)) : False := by
  obtain ⟨c,w,H⟩ := trace_path hn heven ht
  have hm := H.mass m (by omega)
  have hB := H.bounds m (by omega)
  have hpowpos : 0<(2:Nat)^r := Nat.two_pow_pos r
  have hbase : i+2*n+6≤m := by omega
  have hT : total n<2^(n+3) := by
    unfold total
    rw [Nat.pow_add]
    change 7*2^n<2^n*8
    have hpos := Nat.two_pow_pos n
    omega
  have hr : r≤n+3 := by
    by_cases h : r≤n+3
    · exact h
    · have hpow := Nat.pow_le_pow_right (show 0<2 by decide) (show n+3≤r by omega)
      omega
  let A := n+3-r
  have hAr : A+r=n+3 := by dsimp [A]; omega
  have hscale : (total n:Int)<(2:Int)^(n+3) := by
    have hh : (total n:Int)<((2^(n+3):Nat):Int) := by omega
    push_cast at hh
    exact hh
  have hP : 0<(2:Int)^r := Int.pow_pos (by decide)
  apply no_dyadic_paired_return (fun j => (total n:Int)-n-(i+j:Nat)-3) r (2*n+6) A (n+3) (total n:Int)
    (fun j => c (i+j)) (fun j => c (i+2^r+j)) (fun j => w (i+j)) (fun j => bit W (i+j))
    (by omega)
  · have h0 := H.bounds i (by omega)
    have h1 := H.bounds (i+2^r) (by omega)
    simp only [Nat.add_zero,hAr]
    omega
  · intro j hj; exact bit_binary W (i+j)
  · intro j hj
    simpa only [Nat.add_assoc] using H.stepV (i+j) (by omega)
  · intro j hj
    have hh := H.stepV (i+2^r+j) (by omega)
    have heq : bit W (i+2^r+j)=bit W (i+j) := by simp [bit,hrep j hj]
    rw [heq] at hh
    have hclock : (total n:Int)-n-(i+2^r+j:Nat)-3=(total n:Int)-n-(i+j:Nat)-3-(2:Int)^r := by
      push_cast
      omega
    rw [hclock] at hh
    simpa only [Nat.add_assoc] using hh
  · intro j hj heq
    have hh := H.stepW (i+j) (by omega)
    simpa [heq,Nat.add_assoc] using hh
  · intro j hj; exact H.bounds (i+j) (by omega)
  · exact hscale

#print axioms scale_slope
#print axioms no_small_slope_scaled
#print axioms trace_no_uniform_dyadic_repeat

end BB6.Agent9ReturnGCD
