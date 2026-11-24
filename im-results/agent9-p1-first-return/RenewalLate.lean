import RenewalShadow

namespace BB6.Agent9Renewal
open BB6P1Unit

/-- Continue the exact early phase identity without requiring further
agreement with its wrap bits. The integer z absorbs each real wrap. -/
theorem late_shadow (q d n K L : Nat) (D p a C B : Int)
    (hD : 0<D) (hodd : D%2=1) (hp : 0<p) (hpD : p<D)
    (hdq : d<q) (hclock : (q:Int)=7*(2:Int)^n+a)
    (hdiv : D ∣ (2:Int)^L-1) (hM : 0<(2:Int)^L-1)
    (hC : 0≤C) (hB : 0≤B) (ha : ∀ j : Nat, j≤n → Bound (a+j) C)
    (hinit : Bound (D*(d:Int)-7*(2:Int)^n*p) (D*B))
    (hK : K≤n) (hsmall : D*(2:Int)^K*(B+C)<(2:Int)^n)
    (t : Nat) (ht : K+t≤n) :
    let P := (2:Int)^n
    let M := (2:Int)^L-1
    let R := D*M
    let N := R*(d:Int)-M*a*p-cycleSum D p L
    ∃ z e : Int,
      R*(run q d (K+t):Int)=(2:Int)^(K+t)*N+7*P*R*z+e ∧
      Bound e (R*((2:Int)^t*(2*C+2)-C)) := by
  dsimp only
  let P := (2:Int)^n
  let M := (2:Int)^L-1
  let R := D*M
  let N := R*(d:Int)-M*a*p-cycleSum D p L
  have hP : 0<P := Int.pow_pos (by decide)
  have hMp : 0<M := hM
  have hR : 0<R := Int.mul_pos hD hMp
  change ∃ z e : Int, R*(run q d (K+t):Int)=(2:Int)^(K+t)*N+7*P*R*z+e ∧ Bound e (R*((2:Int)^t*(2*C+2)-C))
  induction t with
  | zero =>
    simp only [Nat.add_zero,Int.pow_zero,Int.one_mul]
    have he := (early_shadow q d n K L D p a C B hD hodd hp hpD hdq hclock hdiv hM hC hB ha hinit hK hsmall K (by omega)).2
    let u := orbit D p K
    obtain ⟨z,hz⟩ := orbit_linear D p K
    have hu := orbit_range hD hodd hp hpD K
    have hcyc := cycle_range L hD hodd hu.1 hu.2
    have hcycB : Bound (cycleSum D u L) (2*R) := by
      change 0≤cycleSum D u L ∧ cycleSum D u L≤2*D*M at hcyc
      unfold Bound R
      grind
    have hmu : 0≤M*u := Int.mul_nonneg (by omega) (by omega)
    have hmuC := bound_mul (ha K hK) hmu
    have hmule := Int.mul_le_mul_of_nonneg_left (show u≤D by omega) (show 0≤M by omega)
    have hmule' := Int.mul_le_mul_of_nonneg_right hmule hC
    have hmuB : Bound (M*(a+K)*u) (R*C) := by
      have hb := bound_weaken hmuC (show M*u*C≤R*C by dsimp [R]; grind)
      have hh : M*(a+K)*u=M*u*(a+K) := by ac_rfl
      rwa [hh]
    have hsum := bound_add hmuB hcycB
    refine ⟨-z,M*(a+K)*u+cycleSum D u L,?_,?_⟩
    · change R*(run q d K:Int)=(2:Int)^K*N+7*P*R*(-z)+(M*(a+K)*u+cycleSum D u L)
      change (2:Int)^K*p=u+D*z at hz
      change R*(run q d K:Int)=M*((q:Int)+K)*u+cycleSum D u L+(2:Int)^K*(R*(d:Int)-M*(q:Int)*p-cycleSum D p L) at he
      dsimp [N,R,P,M] at *
      grind
    · exact bound_weaken hsum (by grind)
  | succ t ih =>
    obtain ⟨z,e,he,hb⟩ := ih (by omega)
    let j := K+t
    let x := (bit (q+j) (run q d j):Int)
    have hstep := ibit_equation q d j hdq
    have hx := ibit_range (q+j) (run q d j)
    have hax := bound_bit (ha (j+1) (by omega)) x hx
    have hb' := bound_sub (bound_mul hb (by decide : 0≤(2:Int))) (bound_mul hax (show 0≤R by omega))
    refine ⟨2*z-x,2*e-R*((a+(j+1:Nat))*x),?_,?_⟩
    · change R*(run q d (j+1):Int)=(2:Int)^(j+1)*N+7*P*R*(2*z-x)+(2*e-R*((a+(j+1:Nat))*x))
      change R*(run q d j:Int)=(2:Int)^j*N+7*P*R*z+e at he
      change (run q d (j+1):Int)=2*(run q d j:Int)-((q:Int)+j+1)*x at hstep
      rw [Int.pow_succ]
      push_cast
      grind
    · have heq : 2*(R*((2:Int)^t*(2*C+2)-C))+R*C=R*((2:Int)^(t+1)*(2*C+2)-C) := by rw [Int.pow_succ]; grind
      rw [← heq]
      exact hb'

/-- A nonintegral next phase has a full integer-lattice gap. The scaled
error cannot hide either endpoint when it is smaller than one grid step. -/
theorem separate_phase (R P J S N z e d clock C E : Int)
    (hR : 0<R) (hP : 0<P) (hJ : 0<J) (hS : 0<S) (hPS : P=J*S)
    (hC : 0≤C) (hd : 0≤d) (hdc : d<clock)
    (hc : Bound (clock-7*P) C) (he : Bound e (R*E))
    (hgap : R*(E+C+8)<J) (hN : ¬ (7*R ∣ N))
    (hid : R*d=J*N+7*P*R*z+e) :
    0<N+7*R*S*z ∧ N+7*R*S*z<7*R*S ∧ 2≤d ∧ d+8≤clock := by
  let w := N+7*R*S*z
  have hwid : R*d=J*w+e := by dsimp [w]; grind
  have hw0 : w≠0 := by
    intro hw
    apply hN
    refine ⟨-S*z,?_⟩
    dsimp [w] at hw
    grind
  have hwtop : w≠7*R*S := by
    intro hw
    apply hN
    refine ⟨S*(1-z),?_⟩
    dsimp [w] at hw
    grind
  have hrd : 0≤R*d := Int.mul_nonneg (by omega) hd
  have hRC : 0≤R*C := Int.mul_nonneg (by omega) hC
  have hRE : 0≤R*E := by unfold Bound at he; omega
  have hgap' : R*E+R*C+8*R<J := by grind
  have hwpos : 0<w := by
    by_cases hh : 0<w
    · exact hh
    · have hm := Int.mul_le_mul_of_nonneg_left (show w≤-1 by omega) (show 0≤J by omega)
      unfold Bound at he
      omega
  have hlo := Int.mul_le_mul_of_nonneg_left (show 1≤w by omega) (show 0≤J by omega)
  have hlow : 2≤d := by
    have hmul : R*2≤R*d := by unfold Bound at he; omega
    exact Int.le_of_mul_le_mul_left hmul hR
  have hwlt : w<7*R*S := by
    by_cases hh : w<7*R*S
    · exact hh
    · have hwge : 7*R*S+1≤w := by omega
      have hm := Int.mul_le_mul_of_nonneg_left hwge (show 0≤J by omega)
      have heq : J*(7*R*S+1)=7*P*R+J := by grind
      rw [heq] at hm
      have hclock : d≤7*P+C := by unfold Bound at hc; omega
      have hmul := Int.mul_le_mul_of_nonneg_left hclock (show 0≤R by omega)
      have heq' : R*(7*P+C)=7*P*R+R*C := by grind
      rw [heq'] at hmul
      unfold Bound at he
      omega
  have hhi := Int.mul_le_mul_of_nonneg_left (show w≤7*R*S-1 by omega) (show 0≤J by omega)
  have heq : J*(7*R*S-1)=7*P*R-J := by grind
  rw [heq] at hhi
  have hc' : 7*P-C≤clock := by unfold Bound at hc; omega
  have hcm := Int.mul_le_mul_of_nonneg_left hc' (show 0≤R by omega)
  have hcm' : R*(7*P-C)=7*P*R-R*C := by grind
  rw [hcm'] at hcm
  have hmargin : R*(d+8)≤R*clock := by
    unfold Bound at he
    rw [Int.mul_add]
    omega
  exact ⟨hwpos,hwlt,hlow,Int.le_of_mul_le_mul_left hmargin hR⟩

#print axioms late_shadow
#print axioms separate_phase
end BB6.Agent9Renewal
