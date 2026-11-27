import ReturnObstruction

namespace BB6.Agent9ReturnGCD

/-- A slope divisible by a power of two forces divisibility of all
    states for which at least that many successor bits remain. -/
theorem slope_divisible (g : Int) (a x : Nat→Int) (L r : Nat) (h : Int)
    (hg : g=(2:Int)^r*h)
    (hs : ∀ j<L, 2*a (j+1)=a j+g*x j) :
    ∀ i, i+r≤L → (2:Int)^r ∣ a i := by
  induction r generalizing h with
  | zero => intro i hi; simp
  | succ r ih =>
    intro i hi
    have hg' : g=(2:Int)^r*(2*h) := by rw [hg,Int.pow_succ]; ac_rfl
    obtain ⟨t,ht⟩ := ih (2*h) hg' (i+1) (by omega)
    have hstep := hs i (by omega)
    rw [ht,hg] at hstep
    refine ⟨t-h*x i,?_⟩
    rw [Int.mul_sub,←Int.mul_assoc]
    have hmul : 2*((2:Int)^r*t)=(2:Int)^(r+1)*t := by rw [Int.pow_succ]; ac_rfl
    rw [hmul] at hstep
    omega

/-- Trim the last r positions, divide a slope g=2^r*h by 2^r,
    and apply the odd-slope obstruction. -/
theorem no_small_slope (q dir C : Int) (g : Int) (h L A r B : Nat)
    (a c w x : Nat→Int)
    (hdir : dir=1∨dir= -1) (hodd : h%2=1)
    (hg : g=(2:Int)^r*(h:Int)) (hL : A+r+2*h+B≤L)
    (hinit : -(2:Int)^A<a 0 ∧ a 0<g+(2:Int)^A)
    (hx : ∀ j<L, x j=0∨x j=1)
    (hs : ∀ j<L, 2*c (j+1)=c j+(q+dir*(j:Int))*x j)
    (hw : ∀ j<L, x j=1 → 2*w (j+1)=w j)
    (ha : ∀ j<L, 2*a (j+1)=a j+g*x j)
    (hbound : ∀ j≤L, 1≤c j ∧ c j≤C ∧ 1≤w j ∧ w j≤C)
    (hscale : (h:Int)*(C+(h:Int))<(2:Int)^B) : False := by
  let P : Int := 2^r
  have hP : 0<P := Int.pow_pos (by decide)
  have hg0 : 0≤g := by rw [hg]; exact Int.mul_nonneg (by omega : 0≤P) (by omega)
  have hconf := slope_confined g a x A hg0 (fun j hj => hx j (by omega)) (fun j hj => ha j (by omega)) hinit
  let a' : Nat→Int := fun j => a (A+j)/P
  have hm : ∀ j≤L-A-r, P*a' j=a (A+j) := by
    intro j hj
    have hd : P ∣ a (A+j) := slope_divisible g a x L r (h:Int) hg ha (A+j) (by omega)
    dsimp [a']
    rw [Int.mul_comm]
    exact Int.ediv_mul_cancel hd
  apply no_small_odd_slope (q+dir*(A:Int)) dir C h (L-A-r) B a'
    (fun j => c (A+j)) (fun j => w (A+j)) (fun j => x (A+j)) hdir hodd (by omega)
  · constructor
    · exact Int.ediv_nonneg hconf.1 (by omega)
    · apply Int.ediv_le_of_le_mul hP
      rw [Int.mul_comm]
      exact hg ▸ hconf.2
  · intro j hj; exact hx (A+j) (by omega)
  · intro j hj
    have hh := hs (A+j) (by omega)
    simp only [Int.natCast_add,Int.mul_add] at hh
    simpa only [Nat.add_assoc,Int.add_assoc] using hh
  · intro j hj hx1
    simpa only [Nat.add_assoc] using hw (A+j) (by omega) hx1
  · intro j hj
    have hh := ha (A+j) (by omega)
    rw [show A+j+1=A+(j+1) by omega,←hm j (by omega),←hm (j+1) (by omega),hg] at hh
    change 2*(P*a' (j+1))=P*a' j+(P*(h:Int))*x (A+j) at hh
    apply Int.eq_of_mul_eq_mul_left (show P≠0 by omega)
    rw [Int.mul_add]
    simpa only [show P*(2*a' (j+1))=2*(P*a' (j+1)) by ac_rfl,Int.mul_assoc] using hh
  · intro j hj; exact hbound (A+j) (by omega)
  · exact hscale

/-- Complete separated-return certificate with arbitrary nonzero clock
    gcd. The Bezout witness is supplied explicitly. -/
theorem no_small_gcd_returns (q dir C p s u v g : Int) (h L A r B : Nat)
    (c d e w x : Nat→Int)
    (hdir : dir=1∨dir= -1) (hodd : h%2=1)
    (hbez : u*p+v*s=g) (hg : g=(2:Int)^r*(h:Int))
    (hL : A+r+2*h+B≤L)
    (hinit : -(2:Int)^A<u*(d 0-c 0)+v*(e 0-c 0) ∧
      u*(d 0-c 0)+v*(e 0-c 0)<g+(2:Int)^A)
    (hx : ∀ j<L, x j=0∨x j=1)
    (hs : ∀ j<L, 2*c (j+1)=c j+(q+dir*(j:Int))*x j)
    (hd : ∀ j<L, 2*d (j+1)=d j+(q+dir*(j:Int)+p)*x j)
    (he : ∀ j<L, 2*e (j+1)=e j+(q+dir*(j:Int)+s)*x j)
    (hw : ∀ j<L, x j=1 → 2*w (j+1)=w j)
    (hbound : ∀ j≤L, 1≤c j ∧ c j≤C ∧ 1≤w j ∧ w j≤C)
    (hscale : (h:Int)*(C+(h:Int))<(2:Int)^B) : False := by
  apply no_small_slope q dir C g h L A r B
    (fun j => u*(d j-c j)+v*(e j-c j)) c w x hdir hodd hg hL hinit hx hs hw
  · exact common_word_slope (fun j => q+dir*(j:Int)) p s u v g c d e x L hbez hx hs hd he
  · exact hbound
  · exact hscale

#print axioms no_small_slope
#print axioms no_small_gcd_returns

end BB6.Agent9ReturnGCD
