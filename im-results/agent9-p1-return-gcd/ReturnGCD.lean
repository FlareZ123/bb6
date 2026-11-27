import Lean

namespace BB6.Agent9ReturnGCD

/-- A finite integer sequence satisfying f(j) ≤ 2*f(j+1). -/
theorem growth (f : Nat → Int) (L : Nat)
    (hs : ∀ j<L, f j ≤ 2*f (j+1)) :
    f 0 ≤ (2:Int)^L*f L := by
  have h : ∀ j≤L, f 0 ≤ (2:Int)^j*f j := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      have hj' : j<L := by omega
      have hmul := Int.mul_le_mul_of_nonneg_left (hs j hj')
        (show 0≤(2:Int)^j from Int.pow_nonneg (by decide))
      calc
        f 0 ≤ (2:Int)^j*f j := ih (by omega)
        _ ≤ (2:Int)^j*(2*f (j+1)) := hmul
        _ = (2:Int)^(j+1)*f (j+1) := by rw [Int.pow_succ]; ac_rfl
  exact h L (by omega)

/-- Any integer affine slope forced by a common bit word is confined to
    [0,g] after logarithmically many steps. -/
theorem slope_confined (g : Int) (a x : Nat → Int) (A : Nat)
    (hg : 0≤g)
    (hx : ∀ j<A, x j=0 ∨ x j=1)
    (hs : ∀ j<A, 2*a (j+1)=a j+g*x j)
    (ha : -(2:Int)^A < a 0 ∧ a 0 < g+(2:Int)^A) :
    0≤a A ∧ a A≤g := by
  have h1 := growth a A (by
    intro j hj
    have he := hs j hj
    rcases hx j hj with h|h <;> rw [h] at he <;> simp at he <;> omega)
  let f : Nat → Int := fun j => g-a j
  have h2 := growth f A (by
    intro j hj
    have he := hs j hj
    dsimp [f]
    rcases hx j hj with h|h <;> rw [h] at he <;> simp at he <;> omega)
  dsimp [f] at h2
  have hp : 0≤(2:Int)^A := Int.pow_nonneg (by decide : 0≤(2:Int))
  constructor
  · by_cases hneg : 0≤a A
    · exact hneg
    · have hh := Int.mul_le_mul_of_nonneg_left (show a A≤ -1 by omega) hp
      simp only [Int.mul_neg,Int.mul_one] at hh
      omega
  · by_cases hneg : a A≤g
    · exact hneg
    · have hh := Int.mul_le_mul_of_nonneg_left (show g-a A≤ -1 by omega) hp
      simp only [Int.mul_neg,Int.mul_one] at hh
      omega

/-- A unit affine slope confined to {0,1} fixes every subsequent bit. -/
theorem unit_lock (a x : Nat → Int) (A B : Nat)
    (h0 : a A=0 ∨ a A=1)
    (hx : ∀ j<A+B, x j=0 ∨ x j=1)
    (hs : ∀ j<A+B, 2*a (j+1)=a j+x j) :
    ∀ j<B, x (A+j)=a A := by
  have h : ∀ j≤B, a (A+j)=a A := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      have hstep := hs (A+j) (by omega)
      have he := ih (by omega)
      have hbit := hx (A+j) (by omega)
      rw [he] at hstep
      rw [show A+(j+1)=A+j+1 by omega]
      rcases h0 with h|h <;> rcases hbit with h'|h' <;> omega
  intro j hj
  have hstep := hs (A+j) (by omega)
  have h1 := h j (by omega)
  have h2 := h (j+1) (by omega)
  rw [show A+(j+1)=A+j+1 by omega] at h2
  omega

/-- A strict-interior modular carry word cannot have a long constant tail. -/
theorem no_constant_tail (q : Int) (c x : Nat → Int) (A B : Nat)
    (hc : ∀ j≤A+B, 1≤c j ∧ c j≤q+(j:Int)-3)
    (hs : ∀ j<A+B, 2*c (j+1)=c j+(q+(j:Int))*x j)
    (b : Int) (hb : b=0 ∨ b=1)
    (hconst : ∀ j<B, x (A+j)=b)
    (hscale : q+(A:Int)-3 < (2:Int)^B) : False := by
  rcases hb with hb|hb
  · let f : Nat → Int := fun j => c (A+j)
    have hf : ∀ j<B, -f j≤2*(-f (j+1)) := by
      intro j hj
      have he := hs (A+j) (by omega)
      rw [hconst j hj,hb,Int.mul_zero,Int.add_zero] at he
      dsimp [f]
      rw [show A+(j+1)=A+j+1 by omega]
      omega
    have hh := growth (fun j => -f j) B hf
    have hbnd := hc (A+B) (by omega)
    have hp : 0≤(2:Int)^B := Int.pow_nonneg (by decide : 0≤(2:Int))
    have hm := Int.mul_le_mul_of_nonneg_left (show -f B≤ -1 by dsimp [f]; omega) hp
    simp only [Int.mul_neg,Int.mul_one] at hm
    have hca := hc A (by omega)
    have hbound : f 0≤q+(A:Int)-3 := by dsimp [f]; omega
    change -f 0 ≤ (2:Int)^B*(-f B) at hh
    rw [Int.mul_neg] at hh
    omega
  · let f : Nat → Int := fun j => q+((A+j:Nat):Int)-2-c (A+j)
    have hf : ∀ j<B, -f j≤2*(-f (j+1)) := by
      intro j hj
      have he := hs (A+j) (by omega)
      rw [hconst j hj,hb,Int.mul_one] at he
      dsimp [f]
      rw [show A+(j+1)=A+j+1 by omega]
      omega
    have hh := growth (fun j => -f j) B hf
    have hbnd := hc (A+B) (by omega)
    have hp : 0≤(2:Int)^B := Int.pow_nonneg (by decide : 0≤(2:Int))
    have hm := Int.mul_le_mul_of_nonneg_left (show -f B≤ -1 by dsimp [f]; omega) hp
    simp only [Int.mul_neg,Int.mul_one] at hm
    have hca := hc A (by omega)
    have hbound : f 0≤q+(A:Int)-3 := by dsimp [f]; omega
    change -f 0 ≤ (2:Int)^B*(-f B) at hh
    rw [Int.mul_neg] at hh
    omega

/-- Three copies of the same word induce an integer affine slope by
    any Bezout combination of their clock differences. -/
theorem common_word_slope (clock : Nat → Int) (p s u v g : Int) (c d e x : Nat → Int)
    (L : Nat)
    (hbez : u*p+v*s=g)
    (hx : ∀ j<L, x j=0 ∨ x j=1)
    (hc : ∀ j<L, 2*c (j+1)=c j+clock j*x j)
    (hd : ∀ j<L, 2*d (j+1)=d j+(clock j+p)*x j)
    (he : ∀ j<L, 2*e (j+1)=e j+(clock j+s)*x j) :
    ∀ j<L,
    2*(u*(d (j+1)-c (j+1))+v*(e (j+1)-c (j+1))) =
      u*(d j-c j)+v*(e j-c j)+g*x j := by
  intro j hj
  have h1 := hc j hj
  have h2 := hd j hj
  have h3 := he j hj
  have hD : 2*(d (j+1)-c (j+1))=d j-c j+p*x j := by
    rw [Int.mul_sub]
    rcases hx j hj with h|h <;> rw [h] at h1 h2 ⊢ <;> simp at h1 h2 ⊢ <;> omega
  have hE : 2*(e (j+1)-c (j+1))=e j-c j+s*x j := by
    rw [Int.mul_sub]
    rcases hx j hj with h|h <;> rw [h] at h1 h3 ⊢ <;> simp at h1 h3 ⊢ <;> omega
  calc
    _ = u*(2*(d (j+1)-c (j+1)))+v*(2*(e (j+1)-c (j+1))) := by
      rw [Int.mul_add]
      ac_rfl
    _ = u*(d j-c j+p*x j)+v*(e j-c j+s*x j) := by rw [hD,hE]
    _ = u*(d j-c j)+v*(e j-c j)+(u*p+v*s)*x j := by
      simp only [Int.mul_add,Int.add_mul,Int.mul_assoc]
      ac_rfl
    _ = _ := by rw [hbez]

/-- Explicit coprime-return certificate: the three occurrences may
    overlap or be arbitrarily far apart; only their common bits matter. -/
theorem no_coprime_returns (q p s u v : Int) (c d e x : Nat → Int)
    (A B : Nat)
    (hbez : u*p+v*s=1)
    (hc : ∀ j≤A+B, 1≤c j ∧ c j≤q+(j:Int)-3)
    (hx : ∀ j<A+B, x j=0 ∨ x j=1)
    (hs : ∀ j<A+B, 2*c (j+1)=c j+(q+(j:Int))*x j)
    (hd : ∀ j<A+B, 2*d (j+1)=d j+(q+p+(j:Int))*x j)
    (he : ∀ j<A+B, 2*e (j+1)=e j+(q+s+(j:Int))*x j)
    (ha : -(2:Int)^A < u*(d 0-c 0)+v*(e 0-c 0) ∧
      u*(d 0-c 0)+v*(e 0-c 0) < 1+(2:Int)^A)
    (hscale : q+(A:Int)-3 < (2:Int)^B) : False := by
  let a : Nat → Int := fun j => u*(d j-c j)+v*(e j-c j)
  have hA : ∀ j<A+B, 2*a (j+1)=a j+x j := by
    intro j hj
    simpa [a] using common_word_slope (fun j => q+(j:Int)) p s u v 1 c d e x (A+B) hbez hx hs (fun j hj => by rw [show q+(j:Int)+p=q+p+(j:Int) by omega]; exact hd j hj) (fun j hj => by rw [show q+(j:Int)+s=q+s+(j:Int) by omega]; exact he j hj) j hj
  have hconf := slope_confined 1 a x A (by decide)
    (fun j hj => hx j (by omega))
    (fun j hj => by simpa using hA j (by omega)) ha
  have h0 : a A=0 ∨ a A=1 := by omega
  exact no_constant_tail q c x A B hc hs (a A) h0 (unit_lock a x A B h0 hx hA) hscale

/-- A positive integral coordinate cannot be halved through more bits
    than its initial size permits. -/
theorem no_positive_halves (f : Nat → Int) (B : Nat)
    (hs : ∀ j<B, 2*f (j+1)=f j)
    (he : 1≤f B) (hstart : f 0<(2:Int)^B) : False := by
  have h := growth (fun j => -f j) B (by
    intro j hj
    have h := hs j hj
    omega)
  change -f 0≤(2:Int)^B*(-f B) at h
  rw [Int.mul_neg] at h
  have hm := Int.mul_le_mul_of_nonneg_left he
    (show 0≤(2:Int)^B from Int.pow_nonneg (by decide))
  rw [Int.mul_one] at hm
  omega

/-- A unit slope also obstructs repeated selected words of the full
    decreasing-clock micro dynamics, with no restriction on the delay. -/
theorem no_coprime_paired_returns (clock : Nat → Int) (p s u v : Int)
    (c d e w x : Nat → Int) (A B : Nat)
    (hbez : u*p+v*s=1)
    (hx : ∀ j<A+B, x j=0 ∨ x j=1)
    (hc : ∀ j<A+B, 2*c (j+1)=c j+clock j*x j)
    (hd : ∀ j<A+B, 2*d (j+1)=d j+(clock j+p)*x j)
    (he : ∀ j<A+B, 2*e (j+1)=e j+(clock j+s)*x j)
    (hw : ∀ j<A+B, x j=1 → 2*w (j+1)=w j)
    (ha : -(2:Int)^A < u*(d 0-c 0)+v*(e 0-c 0) ∧
      u*(d 0-c 0)+v*(e 0-c 0) < 1+(2:Int)^A)
    (hend : 1≤c (A+B) ∧ 1≤w (A+B))
    (hscale : c A<(2:Int)^B ∧ w A<(2:Int)^B) : False := by
  let a : Nat → Int := fun j => u*(d j-c j)+v*(e j-c j)
  have hA : ∀ j<A+B, 2*a (j+1)=a j+x j := by
    intro j hj
    simpa [a] using common_word_slope clock p s u v 1 c d e x (A+B) hbez hx hc hd he j hj
  have hconf := slope_confined 1 a x A (by decide)
    (fun j hj => hx j (by omega))
    (fun j hj => by simpa using hA j (by omega)) ha
  have h0 : a A=0 ∨ a A=1 := by omega
  have hlock := unit_lock a x A B h0 hx hA
  rcases h0 with h0|h0
  · apply no_positive_halves (fun j => c (A+j)) B
    · intro j hj
      have hh := hc (A+j) (by omega)
      rw [hlock j hj,h0,Int.mul_zero,Int.add_zero] at hh
      simpa [Nat.add_assoc] using hh
    · exact hend.1
    · simpa using hscale.1
  · apply no_positive_halves (fun j => w (A+j)) B
    · intro j hj
      have hh := hw (A+j) (by omega) ((hlock j hj).trans h0)
      simpa [Nat.add_assoc] using hh
    · exact hend.2
    · simpa using hscale.2

#print axioms no_coprime_paired_returns
#print axioms common_word_slope
#print axioms no_coprime_returns

end BB6.Agent9ReturnGCD
