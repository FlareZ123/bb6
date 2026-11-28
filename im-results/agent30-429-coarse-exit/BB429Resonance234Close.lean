import BB429ResonanceShift
import BB429ResonanceFinite

namespace BB429.CoarseExit

set_option maxHeartbeats 30000000

/-- Drop an arbitrary prefix of exact ordinary phase blocks. -/
theorem phaseBlocks_drop (U V : Nat → Int) (e ph : Nat → Bool) (n j : Nat)
    (hj : j≤n) (hs : PhaseBlocks U V e ph n) :
    PhaseBlocks (fun k => U (j+k)) (fun k => V (j+k))
      (fun k => e (j+k)) (fun k => ph (j+k)) (n-j) := by
  intro i hi
  have h := hs (j+i) (by omega)
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- A prefix consisting entirely of false ordinary blocks is an exact affine
    rescaling: U gains a factor 4 per block and the V-error gains 18. -/
theorem phaseBlocks_false_prefix_values
    (U V : Nat → Int) (e ph : Nat → Bool) (n j : Nat)
    (hj : j≤n) (hs : PhaseBlocks U V e ph n)
    (hf : ∀ k, k<j → e k=false) :
    U j=(4:Int)^j*U 0 ∧ V j=V 0+18*(j:Int) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hjn : j≤n := by omega
      obtain ⟨hu,hv⟩ := ih hjn (fun k hk => hf k (by omega))
      have hs' := hs j (by omega)
      have he : e j=false := hf j (by omega)
      rw [show j+1=Nat.succ j by rfl]
      simp only [he, Bool.false_eq_true, ite_false] at hs'
      rcases hs' with ⟨_, hU, hV⟩
      rw [hU,hV,hu,hv,Int.pow_succ]
      constructor <;> grind +ring

/-- Every positive temporal base-four 0/1 word has a unique initial false
    prefix followed by a nonempty suffix whose first digit is true.  Only the
    existence form is needed by the resonance proof. -/
theorem word4_positive_minimal_suffix (e : Nat → Bool) (I : Nat)
    (hpos : 0<word4 e I) :
    ∃ j i : Nat,
      j+i=I ∧ 1≤i ∧
      (∀ k, k<j → e k=false) ∧ e j=true ∧
      word4 e I = word4 (fun k => e (j+k)) i := by
  induction I generalizing e with
  | zero => simp [word4] at hpos
  | succ I ih =>
      by_cases h0 : e 0=true
      · refine ⟨0,I+1,by omega,by omega,?_,h0,?_⟩
        · intro k hk
          omega
        · simp
      · have h0f : e 0=false := by
          cases h : e 0 <;> simp_all
        have hshift : word4 e (I+1)=word4 (fun k => e (k+1)) I :=
          word4_shift_false e I h0f
        have hpos' : 0<word4 (fun k => e (k+1)) I := by
          simpa [hshift] using hpos
        obtain ⟨j,i,hji,hi,hfalse,htrue,hword⟩ :=
          ih (e := fun k => e (k+1)) hpos'
        refine ⟨j+1,i,by omega,hi,?_,?_,?_⟩
        · intro k hk
          cases k with
          | zero => exact h0f
          | succ k => exact hfalse k (by omega)
        · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htrue
        · rw [hshift,hword]
          congr 2
          funext k
          congr 1
          omega

/-- Complete prefix-stripping package for the remaining doubled d=234
    resonance.  Any resonant word other than the unique short scale m=35 can
    be reduced to a first-true suffix of length i≥7.  At the *original*
    endpoint the low-order V-error is positive and controlled, and the sharp
    minimal-resonance error band survives unchanged.

    This is the previously missing nonminimal-resonance composition step:
    leading false digits no longer form a separate infinite family. -/
theorem d234_resonant_endpoint_package
    (I m n : Nat) (P : Int)
    (U V : Nat → Int) (e ph : Nat → Bool)
    (hIn : I≤n)
    (hm35 : m≠35)
    (hres :
      (2496:Int)*(m:Int)+23808 =
        36+108*word4 e I)
    (hU : U 0=((2496:Int)*(m:Int)+23808)*P)
    (hV : V 0=(54*(4:Int)^I)*P+(108*(m:Int)+777-18*(I:Int)))
    (hs : PhaseBlocks U V e ph n) :
    ∃ i : Nat, 7≤i ∧ i≤I ∧ 5*i+61≤m ∧
      let x := U I-(36*(4:Int)^I)*P
      let z := V I-(54*(4:Int)^I)*P
      let dc := -6*x+4*z+12
      let H := (4:Int)^i
      0≤z ∧ z≤108*(m:Int)+777+24*(i:Int) ∧
      54*H*H < 16*dc ∧ 4*dc≤27*H*H := by
  have hwordpos : 0 < word4 e I := by
    omega
  obtain ⟨j,i,hji,hi,hfalse,hfirst,hword⟩ :=
    word4_positive_minimal_suffix e I hwordpos
  have hiI : i≤I := by
    omega
  have hi7 : 7≤i := by
    by_cases h : 7≤i
    · exact h
    · have hi6 : i≤6 := by omega
      have hm := d234_short_resonance_only35 m i (fun k => e (j+k)) hi6
        (by rw [←hword]; exact hres)
      exact False.elim (hm35 hm)
  let P' : Int := (4:Int)^j*P
  let r' : Int := 54*(4:Int)^i
  let U' : Nat → Int := fun k => U (j+k)
  let V' : Nat → Int := fun k => V (j+k)
  let e' : Nat → Bool := fun k => e (j+k)
  let ph' : Nat → Bool := fun k => ph (j+k)
  have hjn : j≤n := by
    omega
  have hshift := phaseBlocks_drop U V e ph n j hjn hs
  have hs' : PhaseBlocks U' V' e' ph' (n-j) := by
    simpa [U',V',e',ph'] using hshift
  obtain ⟨hUj,hVj⟩ :=
    phaseBlocks_false_prefix_values U V e ph n j hjn hs hfalse
  have hU' : U' 0=((2496:Int)*(m:Int)+23808)*P' := by
    dsimp [U',P']
    rw [hUj,hU]
    grind +ring
  have hpow : (4:Int)^I=(4:Int)^j*(4:Int)^i := by
    rw [←Int.pow_add]
    congr
    omega
  let y' : Int := 108*(m:Int)+777-18*(i:Int)
  have hV' : V' 0=r'*P'+y' := by
    dsimp [V',r',P',y']
    rw [hVj,hV,hpow]
    grind +ring
  have hres' :
      (2496:Int)*(m:Int)+23808 = 36+108*word4 e' i := by
    dsimp [e']
    rw [←hword]
    exact hres
  have hfirst' : e' 0=true := by
    simpa [e'] using hfirst
  have hin' : i≤n-j := by
    omega
  have hgap := d234_minimal_scale_gap i m e' hi7 hfirst' hres'
  have hb := d234_minimal_phase_error_band i m (n-j) P' r' U' V' e' ph'
    hi7 hin' hfirst' hres' hU' (by simpa [y'] using hV') hs'
  have herr := phase_error_bounds P' r'
      ((2496:Int)*(m:Int)+23808) y' (n-j) U' V' e' ph'
      hU' hV' hs' i hin'
  have hlead :
      lead r' ((2496:Int)*(m:Int)+23808) e' i = 36*(4:Int)^i := by
    rw [lead_word4]
    dsimp [r',e']
    rw [←hword]
    rw [hres]
    grind +ring
  refine ⟨i,hi7,hiI,hgap,?_⟩
  dsimp only at hb ⊢
  have hend : j+i=I := hji
  dsimp [U',V',P',r',e',y'] at hb herr
  rw [hend,hlead] at hb herr
  rw [hpow]
  have h36 :
      (36:Int)*(4:Int)^i*((4:Int)^j*P)=
        36*((4:Int)^j*(4:Int)^i)*P := by
    grind +ring
  have h54 :
      (54:Int)*(4:Int)^i*((4:Int)^j*P)=
        54*((4:Int)^j*(4:Int)^i)*P := by
    grind +ring
  rw [←h36,←h54]
  rcases herr with ⟨hzlo,hzhi,_,_⟩
  refine ⟨?_,?_,hb.1,hb.2⟩
  · have hm0 : (0:Int)≤108*(m:Int)+777 := by omega
    omega
  · omega

#print axioms phaseBlocks_drop
#print axioms phaseBlocks_false_prefix_values
#print axioms word4_positive_minimal_suffix
#print axioms d234_resonant_endpoint_package

end BB429.CoarseExit
