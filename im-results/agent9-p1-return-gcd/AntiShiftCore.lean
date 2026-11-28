import Lean
set_option maxHeartbeats 0
namespace BB6.Agent9AntiShift

/-- The pairwise-carry cancellation behind all antiperiodic factors. -/
theorem anti_linear (h d0 d1 k a0 a1 x : Int)
    (hD : 2*d1=d0+k*(1-x))
    (hA : 2*a1=a0+h*x) :
    2*(h*d1+k*a1-k*h)=h*d0+k*a0-k*h := by
  have hf : 2*(h*d1+k*a1-k*h)=h*(2*d1)+k*(2*a1)-2*k*h := by
    simp only [Int.mul_add,Int.mul_sub,Int.mul_assoc]
    ac_rfl
  rw [hf,hD,hA]
  simp only [Int.mul_add,Int.mul_one,Int.mul_sub,Int.sub_eq_add_neg,
    Int.mul_neg,Int.mul_assoc]
  calc
    _ = h*d0+h*k+-(h*k*x)+k*a0+k*h*x+-(2*k*h) := by ac_rfl
    _ = h*d0+k*a0-k*h := by
      have hkx : h*k*x=k*h*x := by ac_rfl
      have hk : h*k=k*h := by ac_rfl
      rw [hkx,hk]
      have hh : (2:Int)*k*h=2*(k*h) := by ac_rfl
      rw [hh]
      omega

/-- If two positive opposite-bit coordinates have a delayed complement
    at offset K, then the mixed determinant halves at every step. -/
theorem antishift_divisibility (h : Int) (q dir : Int) (K B L : Nat)
    (a c w x : Nat→Int)
    (hdir : dir=1∨dir= -1) (hL : K+B≤L)
    (hx : ∀ j<B, x j=0∨x j=1)
    (hflip : ∀ j<B, x (j+K)=1-x j)
    (ha : ∀ j<B, 2*a (j+1)=a j+h*x j)
    (hc : ∀ j<L, 2*c (j+1)=c j+(q+dir*(j:Int))*x j)
    (hw : ∀ j<B, 2*w (j+1)=w j+(q+dir*(j:Int))*(1-x j))
    (hE0 : -(2:Int)^B < h*(c K-w 0)+dir*(K:Int)*a 0-dir*(K:Int)*h ∧
          h*(c K-w 0)+dir*(K:Int)*a 0-dir*(K:Int)*h < (2:Int)^B) :
    h ∣ dir*(K:Int)*(a B-h) := by
  let E : Nat→Int := fun j => h*(c (j+K)-w j)+dir*(K:Int)*a j-dir*(K:Int)*h
  have hhalf : ∀ j<B, 2*E (j+1)=E j := by
    intro j hj
    have hcs := hc (j+K) (by omega)
    have hws := hw j hj
    have hbit := hflip j hj
    have hclock : q+dir*((j+K:Nat):Int)=q+dir*(j:Int)+dir*(K:Int) := by
      simp only [Int.natCast_add,Int.mul_add]
      omega
    rw [hclock,hbit] at hcs
    have hD : 2*(c ((j+1)+K)-w (j+1)) =
      (c (j+K)-w j)+dir*(K:Int)*(1-x j) := by
      rw [show (j+1)+K=j+K+1 by omega]
      rcases hdir with hd|hd <;> rcases hx j hj with hx0|hx1
      · simp [hd,hx0] at hcs hws ⊢; omega
      · simp [hd,hx1] at hcs hws ⊢; omega
      · simp [hd,hx0] at hcs hws ⊢; omega
      · simp [hd,hx1] at hcs hws ⊢; omega
    change 2*(h*(c ((j+1)+K)-w (j+1))+dir*(K:Int)*a (j+1)-dir*(K:Int)*h)=
      h*(c (j+K)-w j)+dir*(K:Int)*a j-dir*(K:Int)*h
    exact anti_linear h (c (j+K)-w j) (c ((j+1)+K)-w (j+1)) (dir*(K:Int))
      (a j) (a (j+1)) (x j) hD (ha j hj)
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
  have hE : -(2:Int)^B<E 0 ∧ E 0<(2:Int)^B := by simpa [E] using hE0
  have hEB : E B=0 := by
    have he := hiter B (by omega)
    have hp : 0<(2:Int)^B := Int.pow_pos (by decide)
    by_cases hneg : E B≤0
    · by_cases heq : E B=0
      · exact heq
      · have hn : E B≤ -1 := by omega
        have hmul := Int.mul_le_mul_of_nonneg_left hn (by omega : 0≤(2:Int)^B)
        rw [Int.mul_neg,Int.mul_one] at hmul
        rw [he] at hE
        omega
    · have hn : 1≤E B := by omega
      have hmul := Int.mul_le_mul_of_nonneg_left hn (by omega : 0≤(2:Int)^B)
      rw [Int.mul_one] at hmul
      rw [he] at hE
      omega
  dsimp [E] at hEB
  refine ⟨-(c (B+K)-w B),?_⟩
  rw [Int.mul_sub, Int.mul_neg]
  omega

#print axioms anti_linear
#print axioms antishift_divisibility
end BB6.Agent9AntiShift
