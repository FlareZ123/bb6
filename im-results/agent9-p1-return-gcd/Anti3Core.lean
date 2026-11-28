import Lean
set_option maxHeartbeats 0

namespace BB6.Agent9Anti3

private theorem hpow (B : Nat) : 0 < (2:Int)^B := Int.pow_pos (by decide)

/-- A slope in the strict interior of the modulus-three carry stays in its
    two-element orbit and the bits alternate. -/
theorem slope3_orbit (b x : Nat → Int) (L : Nat)
    (hinit : b 0 = 1 ∨ b 0 = 2)
    (hx : ∀ j<L, x j=0 ∨ x j=1)
    (hs : ∀ j<L, 2*b (j+1)=b j+3*x j) :
    (∀ j≤L, b j=1 ∨ b j=2) ∧
    (∀ j<L, b (j+1)=3-b j ∧ x j= 2-b j) := by
  have h : ∀ j≤L, b j=1 ∨ b j=2 := by
    intro j hj
    induction j with
    | zero => exact hinit
    | succ j ih =>
      have hprev := ih (by omega)
      have hr := hs j (by omega)
      have hxj := hx j (by omega)
      rcases hprev with h1|h2 <;> rcases hxj with h0|h1' <;> omega
  refine ⟨h,?_⟩
  intro j hj
  have hprev := h j (by omega)
  have hr := hs j hj
  have hxj := hx j hj
  rcases hprev with h1|h2 <;> rcases hxj with h0|h1' <;> omega

/-- If the modulus-three slope is interior then an affine-clock positive
    two-coordinate path cannot sustain an alternating matched factor longer
    than its logarithmic mass bound. -/
theorem no_anti3_interior (q dir C : Int) (B L : Nat)
    (b c w x : Nat → Int)
    (hdir : dir=1 ∨ dir= -1) (hL : B+1≤L)
    (hinit : b 0=1 ∨ b 0=2)
    (hx : ∀ j<L, x j=0 ∨ x j=1)
    (hb : ∀ j<L, 2*b (j+1)=b j+3*x j)
    (hc : ∀ j<L, 2*c (j+1)=c j+(q+dir*(j:Int))*x j)
    (hw : ∀ j<L, 2*w (j+1)=w j+(q+dir*(j:Int))*(1-x j))
    (hbound : ∀ j≤L, 1≤c j ∧ c j≤C ∧ 1≤w j ∧ w j≤C)
    (hscale : 3*(C+1)<(2:Int)^B) : False := by
  obtain ⟨hbval,hborbit⟩ := slope3_orbit b x L hinit hx hb
  have hxflip : ∀ j<B, x (j+1)=1-x j := by
    intro j hj
    have hj0 := (hborbit j (by omega)).2
    have hj1 := (hborbit (j+1) (by omega)).2
    have hstep := (hborbit j (by omega)).1
    omega
  let E : Nat → Int := fun j => 3*(c (j+1)-w j)+dir*b j-3*dir
  have hhalf : ∀ j<B, 2*E (j+1)=E j := by
    intro j hj
    have hcs := hc (j+1) (by omega)
    have hws := hw j (by omega)
    have hbs := hb j (by omega)
    have hxj := hxflip j hj
    change 2*(3*(c ((j+1)+1)-w (j+1))+dir*b (j+1)-3*dir) =
      3*(c (j+1)-w j)+dir*b j-3*dir
    have hclock : (q+dir*((j+1:Nat):Int)) = q+dir*(j:Int)+dir := by
      simp only [Int.natCast_add,Int.natCast_one]
      simp only [Int.mul_add,Int.mul_one]
      omega
    rw [hclock,hxj] at hcs
    rcases hdir with hd|hd <;> rcases hx j (by omega) with hx0|hx1
    · simp [hd,hx0] at hcs hws hbs ⊢
      omega
    · simp [hd,hx1] at hcs hws hbs ⊢
      omega
    · simp [hd,hx0] at hcs hws hbs ⊢
      omega
    · simp [hd,hx1] at hcs hws hbs ⊢
      omega
  have hiter : ∀ j≤B, E 0=(2:Int)^j*E j := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      have he := hhalf j (by omega)
      rw [Int.pow_succ]
      calc
        E 0 = (2:Int)^j*E j := ih (by omega)
        _ = (2:Int)^j*(2*E (j+1)) := by rw [he]
        _ = (2:Int)^j*2*E (j+1) := by ac_rfl
  have h0 := hbound 0 (by omega)
  have h1 := hbound 1 (by omega)
  have hE : -(2:Int)^B < E 0 ∧ E 0 < (2:Int)^B := by
    dsimp [E]
    rcases hdir with hd|hd <;> rw [hd] <;> omega
  have hEB : E B=0 := by
    have he := hiter B (by omega)
    have hp := hpow B
    by_cases hneg : E B≤0
    · by_cases heq : E B=0
      · exact heq
      · have hn : E B ≤ -1 := by omega
        have hmul := Int.mul_le_mul_of_nonneg_left hn (by omega : 0≤(2:Int)^B)
        rw [Int.mul_neg,Int.mul_one] at hmul
        rw [he] at hE
        omega
    · by_cases heq : E B=0
      · exact heq
      · have hn : 1≤E B := by omega
        have hmul := Int.mul_le_mul_of_nonneg_left hn (by omega : 0≤(2:Int)^B)
        rw [Int.mul_one] at hmul
        rw [he] at hE
        omega
  have htail := (hbval B (by omega))
  dsimp [E] at hEB
  rcases hdir with hd|hd
  · rcases htail with hb1|hb2
    · rw [hd,hb1] at hEB
      omega
    · rw [hd,hb2] at hEB
      omega
  · rcases htail with hb1|hb2
    · rw [hd,hb1] at hEB
      omega
    · rw [hd,hb2] at hEB
      omega

#print axioms no_anti3_interior
end BB6.Agent9Anti3
