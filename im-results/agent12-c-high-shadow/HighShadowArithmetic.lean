import Lean.Elab.Tactic.Omega

namespace BB6.Agent12HighShadow

def bits (m : Nat) := 2*m+2
def deficit (j m : Nat) := 3*m+2-j
def oddPart (j m : Nat) := deficit j m % 2
def residual (j m : Nat) := deficit j m - oddPart j m
def directX (j m : Nat) := 3*m+4-j
def directY (j m : Nat) := (j+3*m+7)/2
def bounceX (j m n : Nat) := residual j m / 2^(n+1)+2+oddPart j m
def bounceY (j m n : Nat) := (6*m+14+3*n-bounceX j m n)/2

def directValid (j m : Nat) : Prop :=
  directX j m+j=3*m+4 ∧ 2*directY j m=j+3*m+7

def bounceValid (j m n : Nat) : Prop :=
  2^(n+1)*bounceX j m n = residual j m+2^(n+1)*(2+oddPart j m) ∧
  2*bounceY j m n+bounceX j m n=6*m+14+3*n

instance (j m : Nat) : Decidable (directValid j m) := by unfold directValid; infer_instance
instance (j m n : Nat) : Decidable (bounceValid j m n) := by unfold bounceValid; infer_instance

def admissible (j m v : Nat) : Prop :=
  2≤j ∧ j≤3*m ∧ 2≤m ∧
  v+1≤bits m ∧ residual j m%2^(v+1)=2^v
instance (j m v : Nat) : Decidable (admissible j m v) := by unfold admissible; infer_instance

private theorem cancel_pow (b r p : Nat) (hr : r≤b) (h : 2^b∣2^r*p) : 2^(b-r)∣p := by
  apply Nat.dvd_of_mul_dvd_mul_left (Nat.pow_pos (by decide : 0<(2:Nat)))
  rw [Nat.mul_comm (2^r) (2^(b-r)),Nat.pow_sub_mul_pow 2 hr]
  exact h

private theorem complement_half (p q d : Nat) (hd : 0<d)
    (hq : q%(2*d)=d) (h : 2*d∣p+q) : p%(2*d)=d := by
  have hz := Nat.mod_eq_zero_of_dvd h
  rw [Nat.add_mod,hq] at hz
  have hp := Nat.mod_lt p (by omega : 0<2*d)
  obtain ⟨k,hk⟩ := Nat.dvd_of_mod_eq_zero hz
  have hk1 : k=1 := by
    by_cases hk0 : k=0
    · subst k; omega
    · by_cases hne : k=1
      · exact hne
      · have hge : 2≤k := by omega
        have hmul := Nat.mul_le_mul_left (2*d) hge
        omega
  subst k
  omega

private theorem pow_dvd_product (b r t : Nat) (h : r≤b) : 2^r∣2^b*t :=
  Nat.dvd_trans (Nat.pow_dvd_pow 2 h) (Nat.dvd_mul_right _ _)

/-- The stopping equation determines parity and two small deficits. -/
theorem target_equations (j m k : Nat) (hj : j≤3*m)
    (hstop : k+j+3*m+5=2^(bits m)*(j+3)) :
    (2*j+3+k)%2=oddPart j m ∧
    (2*j+3+k+(2*j+3+k)%2)+residual j m=2^(bits m)*(j+3) ∧
    2*j+3+2*k+6*m+7=2*(2^(bits m)*(j+3)) := by
  have he := Nat.mod_eq_zero_of_dvd (pow_dvd_product (bits m) 1 (j+3) (by unfold bits; omega))
  rw [←hstop] at he
  change (k+j+3*m+5)%2=0 at he
  simp only [oddPart, residual, deficit]
  omega

/-- Sufficient exact valuation and non-power hypotheses for the complete
    original-source inverse-parent grammar. -/
theorem target_valuation (j m k v : Nat) (h : admissible j m v)
    (hstop : k+j+3*m+5=2^(bits m)*(j+3)) :
    5<2*j+3 ∧ 8≤k ∧
    (2*j+3+k+(2*j+3+k)%2)%2^(v+1)=2^v ∧
    2^v<2*j+3+k+(2*j+3+k)%2 := by
  obtain ⟨hj,hj3,hm,hv,hval⟩ := h
  obtain ⟨_,hQ,_⟩ := target_equations j m k hj3 hstop
  have hdiv := pow_dvd_product (bits m) (v+1) (j+3) hv
  rw [←hQ] at hdiv
  have hp : 2^(v+1)=2*2^v := by rw [Nat.pow_succ,Nat.mul_comm]
  have he : 2^(bits m)≤2^(bits m)*(j+3) := by
    simpa using Nat.mul_le_mul_left (2^(bits m)) (show 1≤j+3 by omega)
  have htwo : 2*2^(bits m)≤2^(bits m)*(j+3) := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left (2^(bits m)) (show 2≤j+3 by omega)
  have hpv : 2^(v+1)≤2^(bits m) := Nat.pow_le_pow_right (by decide) hv
  have hmod := complement_half (2*j+3+k+(2*j+3+k)%2) (residual j m) (2^v)
    (Nat.pow_pos (by decide : 0<(2:Nat))) (by rwa [←hp]) (by rwa [←hp])
  have hpow : ∀ r : Nat, 3*r+4≤2^(2*r+2) := by
    intro r
    induction r with
    | zero => decide
    | succ r ih =>
      rw [show 2*(r+1)+2=2*r+2+2 by omega,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega
  have hp_lower : 3*m+4≤2^(bits m) := hpow m
  have hc : residual j m<2^(bits m) := by simp only [residual,oddPart,deficit]; omega
  refine ⟨by omega,?_,by rwa [hp],?_⟩
  · have hbig := Nat.mul_le_mul_right (j+3) hp_lower
    have hprod : (3*m+4)*(j+3)≥j+3*m+13 := by
      have hb := Nat.mul_le_mul_right j (show 1≤3*m+4 by omega)
      rw [Nat.mul_add]
      omega
    omega
  · rw [hp] at hpv
    omega

/-- Each direct parent is congruent to the small positive shadow modulo
    one fewer binary precision bit. -/
theorem direct_bridge (j m k a z : Nat)
    (hstop : k+j+3*m+5=2^(bits m)*(j+3))
    (ha : a+2=2*j+3+k) (hz : 2*z+2=k)
    (hd : directValid j m) :
    2^(bits m-1)∣a+directX j m ∧ 2^(bits m-1)∣z+directY j m := by
  obtain ⟨hA,hB⟩ := hd
  have h1 : a+directX j m=2^(bits m)*(j+3) := by omega
  have h2 : 2*(z+directY j m)=2^(bits m)*(j+3) := by omega
  constructor
  · rw [h1]
    exact pow_dvd_product _ _ _ (by omega)
  · apply cancel_pow (bits m) 1 _ (by unfold bits; omega)
    rw [Nat.pow_one,h2]
    exact Nat.dvd_mul_right _ _

/-- Each high parent is congruent to a small shadow after charging n+2
    bits. The validity equations can be checked on the small integers. -/
theorem bounce_bridge (j m k a z n : Nat) (hj : j≤3*m) (hn : n+2≤bits m)
    (hstop : k+j+3*m+5=2^(bits m)*(j+3))
    (ha : 2*j+3+k+(2*j+3+k)%2=2^(n+1)*(a+2+(2*j+3+k)%2))
    (hz : 2*z+a+7+3*n=2*j+3+2*k)
    (hv : bounceValid j m n) :
    2^(bits m-(n+2))∣a+bounceX j m n ∧ 2^(bits m-(n+2))∣z+bounceY j m n := by
  obtain ⟨ho,hQ,hW⟩ := target_equations j m k hj hstop
  obtain ⟨hA,hB⟩ := hv
  have h1 : 2^(n+1)*(a+bounceX j m n)=2^(bits m)*(j+3) := by
    rw [ho] at ha
    simp only [Nat.mul_add] at ha hA hQ ⊢
    omega
  have h2 : 2*(z+bounceY j m n)+(a+bounceX j m n)=2*(2^(bits m)*(j+3)) := by omega
  have h3 : 2^(bits m-(n+1))∣a+bounceX j m n := by
    apply cancel_pow (bits m) (n+1) _ (by omega)
    rw [h1]
    exact Nat.dvd_mul_right _ _
  have h4 : 2^(bits m-(n+1))∣2*(z+bounceY j m n)+(a+bounceX j m n) := by
    rw [h2, Nat.mul_comm 2]
    apply Nat.dvd_trans (pow_dvd_product (bits m) (bits m-(n+1)) (j+3) (by omega))
    exact Nat.dvd_mul_right _ _
  have h5 := Nat.dvd_sub h4 h3
  rw [Nat.add_sub_cancel] at h5
  constructor
  · exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) h3
  · have hh := cancel_pow (bits m-(n+1)) 1 (z+bounceY j m n) (by omega) (by simpa using h5)
    rwa [show bits m-(n+1)-1=bits m-(n+2) by omega] at hh

/-- The only machine-specific input is the necessary parent grammar.
    The shadow checker may use any sound implementation, including a DAG. -/
def highCheck (check : Nat → Nat → Nat → Nat → Bool) (f j m v : Nat) : Bool :=
  decide (admissible j m v) &&
  (if (j+3*m+5)%2=0 then
    decide (directValid j m) && check f (bits m-1) (directX j m) (directY j m)
   else true) &&
  (List.range (v+1)).all (fun n =>
    if n+2≤v ∧ n%2=oddPart j m then
      decide (bounceValid j m n) &&
      check f (bits m-(n+2)) (bounceX j m n) (bounceY j m n)
    else true)

abbrev ParentContract (reach : Nat → Nat → Prop) : Prop :=
  ∀ x y v, 5<x → 8≤y → (x+y+(x+y)%2)%2^(v+1)=2^v →
    2^v<x+y+(x+y)%2 → reach x y → ∃ a z, reach a z ∧
      ((y%2=0 ∧ a+2=x+y ∧ 2*z+2=y) ∨
      ∃ n, n+2≤v ∧ n%2=(x+1+(x+y)%2)%2 ∧
        x+y+(x+y)%2=2^(n+1)*(a+2+(x+y)%2) ∧
        2*z+a+7+3*n=x+2*y)

abbrev ShadowContract (reach : Nat → Nat → Prop)
    (check : Nat → Nat → Nat → Nat → Bool) : Prop :=
  ∀ f b x y sx sy, check f b sx sy=true →
    2^b∣x+sx → 2^b∣y+sy → ¬reach x y

/-- All exact source parents are covered without constructing the exponential
    stopping target in the executable checker. -/
theorem highCheck_sound (reach : Nat → Nat → Prop)
    (check : Nat → Nat → Nat → Nat → Bool)
    (parent : ParentContract reach) (sound : ShadowContract reach check)
    (f j m v k : Nat) (h : highCheck check f j m v=true)
    (hstop : k+j+3*m+5=2^(bits m)*(j+3)) : ¬reach (2*j+3) k := by
  intro hr
  simp only [highCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨had,hd⟩,hh⟩ := h
  obtain ⟨hx,hy,hval,hgt⟩ := target_valuation j m k v had hstop
  obtain ⟨_,hj,_,hv,_⟩ := had
  obtain ⟨ho,_,_⟩ := target_equations j m k hj hstop
  obtain ⟨a,z,hreach,hp⟩ := parent (2*j+3) k v hx hy hval hgt hr
  rcases hp with ⟨hk,ha,hz⟩ | ⟨n,hn,hpar,ha,hz⟩
  · have he := Nat.mod_eq_zero_of_dvd (pow_dvd_product (bits m) 1 (j+3) (by unfold bits; omega))
    rw [←hstop] at he
    have hc : (j+3*m+5)%2=0 := by change (k+j+3*m+5)%2=0 at he; omega
    simp only [hc,ite_true,Bool.and_eq_true,decide_eq_true_eq] at hd
    obtain ⟨ha',hz'⟩ := direct_bridge j m k a z hstop ha hz hd.1
    exact sound f _ a z _ _ hd.2 ha' hz' hreach
  · have hpar' : n%2=oddPart j m := by
      rw [ho] at hpar
      have hodd : oddPart j m<2 := Nat.mod_lt _ (by decide)
      omega
    have hmem : n∈List.range (v+1) := List.mem_range.mpr (by omega)
    have hchk := (List.all_eq_true.mp hh) n hmem
    rw [if_pos (show n+2≤v ∧ n%2=oddPart j m from ⟨hn,hpar'⟩)] at hchk
    simp only [Bool.and_eq_true,decide_eq_true_eq] at hchk
    obtain ⟨ha',hz'⟩ := bounce_bridge j m k a z n hj (by omega) hstop ha hz hchk.1
    exact sound f _ a z _ _ hchk.2 ha' hz' hreach

#print axioms highCheck_sound
#print axioms target_equations
#print axioms target_valuation
#print axioms direct_bridge
#print axioms bounce_bridge
end BB6.Agent12HighShadow
