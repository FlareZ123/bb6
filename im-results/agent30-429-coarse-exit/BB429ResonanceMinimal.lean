import BB429ResonanceErrorBand

namespace BB429.CoarseExit

set_option maxHeartbeats 20000000


/-- A minimal d=234 second-resonance word is exponentially shorter than its
    scale.  The deliberately weak linear consequence m ≥ 5i+61 is already
    enough to make the final geometric-cycle margin enormous. -/
theorem d234_minimal_scale_gap
    (i m : Nat) (e : Nat → Bool)
    (hi7 : 7≤i) (hfirst : e 0=true)
    (hres :
      (2496:Int)*(m:Int)+23808 =
        36+108*word4 e i) :
    5*i+61≤m := by
  have hw := word4_first_true e i (by omega) hfirst
  have hp := pow4_ge_500_index i hi7
  have hp' : (500:Int)*(i:Int)≤(4:Int)^(i-1) := by
    exact_mod_cast hp
  have hb : (500:Int)*(i:Int)≤word4 e i := by omega
  have hiI : (7:Int)≤(i:Int) := by exact_mod_cast hi7
  have hmI : (5:Int)*(i:Int)+61≤(m:Int) := by
    omega
  exact_mod_cast hmI

/-- The abstract error band specialized to a *minimal* d=234 doubled-scale
    resonance word.  Minimal means the first temporal base-four digit is
    true; for length at least seven this alone supplies all large-scale
    inequalities required by d234_error_band_arith. -/
theorem d234_minimal_phase_error_band
    (i m n : Nat) (P r : Int)
    (U V : Nat → Int) (e ph : Nat → Bool)
    (hi7 : 7≤i) (hin : i≤n) (hfirst : e 0=true)
    (hres :
      (2496:Int)*(m:Int)+23808 =
        36+108*word4 e i)
    (hU : U 0=((2496:Int)*(m:Int)+23808)*P)
    (hV : V 0=r*P+(108*(m:Int)+777-18*(i:Int)))
    (hs : PhaseBlocks U V e ph n) :
    let x := U i-lead r ((2496:Int)*(m:Int)+23808) e i*P
    let z := V i-r*P
    let dc := -6*x+4*z+12
    let H := (4:Int)^i
    54*H*H < 16*dc ∧ 4*dc≤27*H*H := by
  dsimp only
  let b := word4 e i
  let H : Int := 4^i
  let y : Int := 108*(m:Int)+777-18*(i:Int)
  have hb := word4_bound e i
  have hfirst' := word4_first_true e i (by omega) hfirst
  have hp500 := pow4_ge_500_index i hi7
  have hp500' : (500:Int)*(i:Int)≤(4:Int)^(i-1) := by
    exact_mod_cast hp500
  have hHstep : H=4*(4:Int)^(i-1) := by
    dsimp [H]
    rw [show i=(i-1)+1 by omega,Int.pow_succ]
    ring
  have hhlo : H≤4*b := by
    dsimp [b]
    rw [hHstep]
    omega
  have hh0 : 0≤H := Int.pow_nonneg (by decide)
  have hhhi : 3*b+1≤H := by
    dsimp [b,H]
    exact hb.2
  have hlo : 500*(i:Int)≤b := by
    dsimp [b]
    omega
  have hbig : (3500:Int)≤b := by
    have hiI : (7:Int)≤(i:Int) := by exact_mod_cast hi7
    omega
  have hb0 : 0≤b := by dsimp [b]; exact hb.1
  have hrel : 9*b=208*(m:Int)+1981 := by
    dsimp [b] at hres ⊢
    omega
  have herr := phase_error_bounds P r
    ((2496:Int)*(m:Int)+23808) y n U V e ph
    (by simpa [y] using hU) (by simpa [y] using hV) hs i hin
  obtain ⟨hzlo,hzhi,hxlo,hxhi⟩ := herr
  exact d234_error_band_arith i m b H y
    (U i-lead r ((2496:Int)*(m:Int)+23808) e i*P)
    (V i-r*P)
    (-6*(U i-lead r ((2496:Int)*(m:Int)+23808) e i*P)+
      4*(V i-r*P)+12)
    hi7 hb0 hlo hbig hhlo hh0 hhhi hrel rfl
    hxlo hxhi hzlo hzhi rfl

#print axioms d234_minimal_scale_gap
#print axioms d234_minimal_phase_error_band

end BB429.CoarseExit
