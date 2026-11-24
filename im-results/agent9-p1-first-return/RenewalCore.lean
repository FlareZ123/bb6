import ReverseUnitMap

namespace BB6.Agent9Renewal
open BB6P1Unit

-- A finite, constant-modulus binary cycle; no infinite series is required.
def nxt (D p : Int) : Int := (2*p)%D

def orbit (D p : Int) : Nat → Int
  | 0 => p
  | j+1 => orbit D (nxt D p) j

theorem orbit_step (D p : Int) (j : Nat) :
    orbit D p (j+1)=nxt D (orbit D p j) := by
  induction j generalizing p with
  | zero => rfl
  | succ j ih =>
    simp only [orbit]
    exact ih (nxt D p)

theorem nxt_range {D p : Int} (hD : 0<D) (hodd : D%2=1)
    (hp : 0<p) (hpD : p<D) : 0<nxt D p ∧ nxt D p<D := by
  unfold nxt
  by_cases h : 2*p<D
  · rw [Int.emod_eq_of_lt (by omega) h]
    omega
  · rw [← Int.sub_emod_right (2*p) D,
      Int.emod_eq_of_lt (by omega) (by omega : 2*p-D<D)]
    omega

theorem orbit_range {D p : Int} (hD : 0<D) (hodd : D%2=1)
    (hp : 0<p) (hpD : p<D) (j : Nat) : 0<orbit D p j ∧ orbit D p j<D := by
  induction j with
  | zero => exact ⟨hp,hpD⟩
  | succ j ih => rw [orbit_step]; exact nxt_range hD hodd ih.1 ih.2

theorem orbit_linear (D p : Int) (j : Nat) :
    ∃ z : Int, (2:Int)^j*p=orbit D p j+D*z := by
  induction j with
  | zero => exact ⟨0,by simp [orbit]⟩
  | succ j ih =>
    obtain ⟨z,hz⟩ := ih
    let w := orbit D p j
    refine ⟨2*z+(2*w)/D,?_⟩
    have hmod := Int.emod_add_mul_ediv (2*w) D
    rw [orbit_step]
    change (2:Int)^(j+1)*p=(2*w)%D+D*(2*z+(2*w)/D)
    rw [Int.pow_succ]
    grind

theorem orbit_period {D p : Int} (L : Nat) (hD : 0<D) (hodd : D%2=1)
    (hp : 0<p) (hpD : p<D) (hdiv : D ∣ (2:Int)^L-1) : orbit D p L=p := by
  obtain ⟨z,hz⟩ := orbit_linear D p L
  obtain ⟨t,ht⟩ := hdiv
  have hr := orbit_range hD hodd hp hpD L
  have he : orbit D p L-p=D*(t*p-z) := by grind
  have hh : -D< D*(t*p-z) ∧ D*(t*p-z)<D := by omega
  by_cases h : 0<t*p-z
  · have hm := Int.mul_le_mul_of_nonneg_left (show 1≤t*p-z by omega) (show 0≤D by omega)
    omega
  · by_cases h' : t*p-z<0
    · have hm := Int.mul_le_mul_of_nonneg_left (show t*p-z≤-1 by omega) (show 0≤D by omega)
      omega
    · have hz' : t*p-z=0 := by omega
      rw [hz',Int.mul_zero] at he
      omega

def cycleSum (D p : Int) : Nat → Int
  | 0 => 0
  | L+1 => (2:Int)^(L+1)*p+cycleSum D (nxt D p) L

theorem cycle_shift_raw (D p : Int) (L : Nat) :
    cycleSum D (nxt D p) L+(2:Int)^(L+1)*p =
      2*cycleSum D p L+2*orbit D p L := by
  induction L generalizing p with
  | zero => simp [cycleSum,orbit]
  | succ L ih =>
    simp only [cycleSum,orbit]
    have hh := ih (nxt D p)
    rw [Int.pow_succ (2:Int) (L+1)]
    grind

theorem cycle_shift {D p : Int} (L : Nat) (hD : 0<D) (hodd : D%2=1)
    (hp : 0<p) (hpD : p<D) (hdiv : D ∣ (2:Int)^L-1) :
    cycleSum D (nxt D p) L+2*((2:Int)^L-1)*p=2*cycleSum D p L := by
  have hh := cycle_shift_raw D p L
  rw [orbit_period L hD hodd hp hpD hdiv,Int.pow_succ] at hh
  grind

theorem cycle_range {D p : Int} (L : Nat) (hD : 0<D) (hodd : D%2=1)
    (hp : 0<p) (hpD : p<D) :
    0≤cycleSum D p L ∧ cycleSum D p L≤2*D*((2:Int)^L-1) := by
  induction L generalizing p with
  | zero => simp [cycleSum]
  | succ L ih =>
    have hn := nxt_range hD hodd hp hpD
    have hi := ih hn.1 hn.2
    have hpow : 0≤(2:Int)^(L+1) := Int.pow_nonneg (by decide)
    have hm := Int.mul_le_mul_of_nonneg_left (show p≤D by omega) hpow
    have hp0 := Int.mul_nonneg hpow (show 0≤p by omega)
    simp only [cycleSum]
    rw [Int.pow_succ] at hm ⊢
    constructor <;> grind

theorem cycle_linear (D p : Int) (L : Nat) :
    ∃ z : Int, cycleSum D p L=(L:Int)*(2:Int)^L*p+D*z := by
  induction L generalizing p with
  | zero => exact ⟨0,by simp [cycleSum]⟩
  | succ L ih =>
    obtain ⟨z,hz⟩ := ih (nxt D p)
    let v := (2*p)/D
    refine ⟨z-(L:Int)*(2:Int)^L*v,?_⟩
    have hn : nxt D p=2*p-D*v := by
      have hh := Int.emod_add_mul_ediv (2*p) D
      unfold nxt v
      omega
    simp only [cycleSum,hn,Int.pow_succ,Int.natCast_succ]
    grind

theorem cycle_mod {D p : Int} (L : Nat) (hdiv : D ∣ (2:Int)^L-1) :
    ∃ z : Int, cycleSum D p L=(L:Int)*p+D*z := by
  obtain ⟨z,hz⟩ := cycle_linear D p L
  obtain ⟨t,ht⟩ := hdiv
  exact ⟨z+(L:Int)*t*p,by grind⟩

#print axioms cycle_shift
#print axioms cycle_range
#print axioms cycle_mod
end BB6.Agent9Renewal
