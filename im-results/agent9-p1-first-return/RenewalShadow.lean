import RenewalCore

namespace BB6.Agent9Renewal
open BB6P1Unit

def Bound (x R : Int) : Prop := -R≤x ∧ x≤R

theorem bound_add {x y R S : Int} (hx : Bound x R) (hy : Bound y S) :
    Bound (x+y) (R+S) := by unfold Bound at *; omega

theorem bound_sub {x y R S : Int} (hx : Bound x R) (hy : Bound y S) :
    Bound (x-y) (R+S) := by unfold Bound at *; omega

theorem bound_mul {x R c : Int} (hx : Bound x R) (hc : 0≤c) :
    Bound (c*x) (c*R) := by
  unfold Bound at *
  have hlo := Int.mul_le_mul_of_nonneg_left hx.1 hc
  have hhi := Int.mul_le_mul_of_nonneg_left hx.2 hc
  rw [Int.mul_neg] at hlo
  exact ⟨hlo,hhi⟩

theorem bound_weaken {x R S : Int} (hx : Bound x R) (hRS : R≤S) :
    Bound x S := by unfold Bound at *; omega

theorem bound_bit {x R : Int} (hx : Bound x R) (b : Int) (hb : b=0 ∨ b=1) :
    Bound (x*b) R := by
  have hR : 0≤R := by unfold Bound at hx; omega
  rcases hb with hb | hb <;> rw [hb] <;> simp [Bound] at * <;> omega

theorem pow_mono {i j : Nat} (h : i≤j) : (2:Int)^i≤(2:Int)^j := by
  exact_mod_cast Nat.pow_le_pow_right (show 0<2 by decide) h

theorem one_le_two_pow (j : Nat) : (1:Int)≤(2:Int)^j := by
  exact_mod_cast Nat.one_le_pow j 2 (by decide)

theorem ibit_range (q d : Nat) : (bit q d : Int)=0 ∨ (bit q d : Int)=1 := by
  unfold bit
  split <;> simp

theorem ibit_equation (q d j : Nat) (hdq : d<q) :
    (run q d (j+1):Int)=2*(run q d j:Int)-((q:Int)+j+1)*(bit (q+j) (run q d j):Int) := by
  have he := unit_equation (q+j) (run q d j) (run_lt q d j hdq)
  have hr : run q d (j+1)=unit (q+j) (run q d j) := rfl
  rw [← hr] at he
  have hi := congrArg (fun x : Nat => (x:Int)) he
  push_cast at hi
  omega

def cbit (D p : Int) : Int := if D≤2*p then 1 else 0

theorem cbit_range (D p : Int) : cbit D p=0 ∨ cbit D p=1 := by
  unfold cbit; split <;> simp

theorem cbit_equation {D p : Int} (hp : 0<p) (hpD : p<D) :
    nxt D p=2*p-D*cbit D p := by
  unfold nxt cbit
  by_cases h : 2*p<D
  · simp [show ¬ D≤2*p by omega,Int.emod_eq_of_lt (by omega : 0≤2*p) h]
  · rw [if_pos (by omega : D≤2*p),Int.mul_one,← Int.sub_emod_right (2*p) D,
        Int.emod_eq_of_lt (by omega) (by omega : 2*p-D<D)]

theorem same_wrap (D P p : Int) (q d : Nat) (a e C R : Int)
    (hD : 0<D) (hP : 0<P) (hodd : D%2=1)
    (hq : (q:Int)+1=7*P+a) (he : D*(d:Int)=7*P*p+e)
    (ha : Bound a C) (heB : Bound e R) (hsmall : 2*R+D*C<7*P) :
    (bit q d : Int)=cbit D p := by
  have hda := bound_mul ha (show 0≤D by omega)
  have hdif : D*(2*(d:Int)-(q:Int)-1)=7*P*(2*p-D)+2*e-D*a := by grind
  unfold Bound at hda heB
  unfold cbit bit
  by_cases hp : D≤2*p
  · have hm := Int.mul_le_mul_of_nonneg_left (show 1≤2*p-D by omega) (show 0≤7*P by omega)
    have hpos : 0<D*(2*(d:Int)-(q:Int)-1) := by omega
    have hx := Int.lt_of_mul_lt_mul_left (show D*0<D*(2*(d:Int)-(q:Int)-1) by simpa using hpos) (show 0≤D by omega)
    simp [hp,show q+1≤2*d by omega]
  · have hm := Int.mul_le_mul_of_nonneg_left (show 2*p-D≤-1 by omega) (show 0≤7*P by omega)
    have hneg : D*(2*(d:Int)-(q:Int)-1)<0 := by omega
    have hx := Int.lt_of_mul_lt_mul_left (show D*(2*(d:Int)-(q:Int)-1)<D*0 by simpa using hneg) (show 0≤D by omega)
    simp [hp,show ¬ q+1≤2*d by omega]

/-- Exact early shadow: every early wrap matches the ideal periodic phase;
its scaled state error and the finite weighted-cycle identity are preserved. -/
theorem early_shadow (q d n K L : Nat) (D p a C B : Int)
    (hD : 0<D) (hodd : D%2=1) (hp : 0<p) (hpD : p<D)
    (hdq : d<q) (hclock : (q:Int)=7*(2:Int)^n+a)
    (hdiv : D ∣ (2:Int)^L-1) (hM : 0<(2:Int)^L-1)
    (hC : 0≤C) (hB : 0≤B) (ha : ∀ j : Nat, j≤n → Bound (a+j) C)
    (hinit : Bound (D*(d:Int)-7*(2:Int)^n*p) (D*B))
    (hK : K≤n) (hsmall : D*(2:Int)^K*(B+C)<(2:Int)^n)
    (j : Nat) (hj : j≤K) :
    Bound (D*(run q d j:Int)-7*(2:Int)^n*orbit D p j) (D*((2:Int)^j*(B+C)-C)) ∧
    D*((2:Int)^L-1)*(run q d j:Int) =
      ((2:Int)^L-1)*((q:Int)+j)*orbit D p j+cycleSum D (orbit D p j) L+
        (2:Int)^j*(D*((2:Int)^L-1)*(d:Int)-((2:Int)^L-1)*(q:Int)*p-cycleSum D p L) := by
  let P := (2:Int)^n
  let M := (2:Int)^L-1
  have hP : 0<P := Int.pow_pos (by decide)
  have hM' : 0<M := hM
  induction j with
  | zero =>
    simp only [run,orbit,Int.natCast_zero,Int.add_zero,Int.pow_zero,Int.one_mul]
    constructor
    · simpa only [show B+C-C=B by omega] using hinit
    · grind
  | succ j ih =>
    obtain ⟨hb,hi⟩ := ih (by omega)
    let u := orbit D p j
    let v := run q d j
    let e := D*(v:Int)-7*P*u
    let R := D*((2:Int)^j*(B+C)-C)
    let x := cbit D u
    have hu := orbit_range hD hodd hp hpD j
    have hb' : Bound e R := hb
    have ha' := ha (j+1) (by omega)
    have hpmono := pow_mono (show j+1≤K by omega)
    have hm := Int.mul_le_mul_of_nonneg_right hpmono (show 0≤B+C by omega)
    have hm' := Int.mul_le_mul_of_nonneg_left hm (show 0≤D by omega)
    have hsmall' : 2*R+D*C<7*P := by
      dsimp [R,P]
      rw [Int.pow_succ] at hm'
      have hDC := Int.mul_nonneg (show 0≤D by omega) hC
      grind
    have hq' : ((q+j:Nat):Int)+1=7*P+(a+(j+1:Nat)) := by push_cast; omega
    have hx := same_wrap D P u (q+j) v (a+(j+1:Nat)) e C R hD hP hodd hq' (by dsimp [e]; omega) ha' hb' hsmall'
    have hstep := ibit_equation q d j hdq
    change (run q d (j+1):Int)=2*(v:Int)-((q:Int)+j+1)*(bit (q+j) v:Int) at hstep
    rw [hx] at hstep
    have hc := cbit_equation hu.1 hu.2
    have hc' := cycle_shift L hD hodd hu.1 hu.2 hdiv
    have hbit := cbit_range D u
    have hbound := bound_sub (bound_mul hb' (by decide : 0≤(2:Int)))
      (bound_mul (bound_bit ha' x hbit) (show 0≤D by omega))
    have herr : D*(run q d (j+1):Int)-7*P*nxt D u=2*e-D*((a+(j+1:Nat))*x) := by
      dsimp [e,x]
      push_cast
      grind
    rw [orbit_step]
    constructor
    · change Bound (D*(run q d (j+1):Int)-7*P*nxt D u) (D*((2:Int)^(j+1)*(B+C)-C))
      rw [herr]
      have heq : 2*R+D*C=D*((2:Int)^(j+1)*(B+C)-C) := by dsimp [R]; rw [Int.pow_succ]; grind
      rwa [← heq]
    · change D*M*(run q d (j+1):Int)=M*((q:Int)+(j+1:Nat))*nxt D u+cycleSum D (nxt D u) L+(2:Int)^(j+1)*(D*M*(d:Int)-M*(q:Int)*p-cycleSum D p L)
      rw [Int.pow_succ]
      push_cast
      grind

#print axioms same_wrap
#print axioms early_shadow
end BB6.Agent9Renewal
