import BB429Resonance

namespace BB429.CoarseExit

/-- Four bounded base-four steps at doubled leading scale.  This is the
    parity companion of `four_edges`: with subtraction 108 and box [0,54],
    the exact four-step survivor set is {0,9,27,36}. -/
theorem four_edges54 (z0 z1 z2 z3 z4 : Int)
    (h0 : 0≤z0 ∧ z0≤54) (h1 : 0≤z1 ∧ z1≤54) (h2 : 0≤z2 ∧ z2≤54)
    (h3 : 0≤z3 ∧ z3≤54) (h4 : 0≤z4 ∧ z4≤54)
    (e0 : z1=4*z0 ∨ z1=4*z0-108) (e1 : z2=4*z1 ∨ z2=4*z1-108)
    (e2 : z3=4*z2 ∨ z3=4*z2-108) (e3 : z4=4*z3 ∨ z4=4*z3-108) :
    z0=0 ∨ z0=9 ∨ z0=27 ∨ z0=36 := by
  rcases e0 with e0|e0 <;>
    rcases e1 with e1|e1 <;>
    rcases e2 with e2|e2 <;>
    rcases e3 with e3|e3 <;> omega

theorem scaled_bounds54 (H z : Int) (hH : 0<H)
    (h : 0≤H*z ∧ H*z≤54*H) : 0≤z ∧ z≤54 := by
  constructor
  · apply Int.le_of_mul_le_mul_left _ hH
    simpa using h.1
  · apply Int.le_of_mul_le_mul_left _ hH
    simpa [Int.mul_comm] using h.2

theorem scaled_step54 (H a r z : Int) (e : Bool) (hr : r=54*H) (ha : a=H*z) :
    4*a-(if e then 2*r else 0)=H*(4*z-(if e then 108 else 0)) := by
  subst r a
  cases e <;> simp [Int.mul_sub,Int.mul_assoc,Int.mul_left_comm,Int.mul_comm] <;> omega

/-- If r=54H, four further bounded leading-coefficient steps force the
    normalized coefficient into the exact set {0,9,27,36}. -/
theorem four_scaled54 (H r a : Int) (e : Nat → Bool) (i : Nat) (z : Int)
    (hH : 0<H) (hr : r=54*H) (hz : lead r a e i=H*z)
    (hb : ∀ j, j≤i+4 → 0≤lead r a e j ∧ lead r a e j≤r) :
    z=0 ∨ z=9 ∨ z=27 ∨ z=36 := by
  let z1 := 4*z-(if e i then 108 else 0)
  let z2 := 4*z1-(if e (i+1) then 108 else 0)
  let z3 := 4*z2-(if e (i+2) then 108 else 0)
  let z4 := 4*z3-(if e (i+3) then 108 else 0)
  have h1 : lead r a e (i+1)=H*z1 := scaled_step54 H _ _ z (e i) hr hz
  have h2 : lead r a e (i+2)=H*z2 := scaled_step54 H _ _ z1 (e (i+1)) hr h1
  have h3 : lead r a e (i+3)=H*z3 := scaled_step54 H _ _ z2 (e (i+2)) hr h2
  have h4 : lead r a e (i+4)=H*z4 := scaled_step54 H _ _ z3 (e (i+3)) hr h3
  have b0 := hb i (by omega); rw [hz,hr] at b0
  have b1 := hb (i+1) (by omega); rw [h1,hr] at b1
  have b2 := hb (i+2) (by omega); rw [h2,hr] at b2
  have b3 := hb (i+3) (by omega); rw [h3,hr] at b3
  have b4 := hb (i+4) (by omega); rw [h4,hr] at b4
  apply four_edges54 z z1 z2 z3 z4
    (scaled_bounds54 _ _ hH b0) (scaled_bounds54 _ _ hH b1)
    (scaled_bounds54 _ _ hH b2) (scaled_bounds54 _ _ hH b3)
    (scaled_bounds54 _ _ hH b4)
  · dsimp only [z1]; split <;> omega
  · dsimp only [z2]; split <;> omega
  · dsimp only [z3]; split <;> omega
  · dsimp only [z4]; split <;> omega

/-- Parity companion of `return_from_exact_burst`.  If the large leading
    V coefficient is 54*4^I rather than 27*4^I, the only possible surviving
    resonance is a = 36 + 108*word4. -/
theorem return_from_exact_burst_even (p : State) (I : Nat) (a P y : Int)
    (hodd : p.2%2=1) (hy : 27≤y) (hU : Uc p=a*P)
    (hV : Vc p=(54*4^I)*P+y)
    (hsep : 3*cap (budget 0 y (I+4)) (I+4)+39<P)
    (ha12 : a%12=0)
    (hres : ∀ e : Nat → Bool, a≠36+108*word4 e I) :
    ∃ k t, 0<k ∧ k≤2*(I+4) ∧ run k p=some t ∧ isSection t := by
  classical
  let L := I+4
  let H : Int := 4^I
  let r : Int := 54*H
  by_cases hex : ∃ k t, 0<k ∧ k≤2*L ∧ run k p=some t ∧ isSection t
  · exact hex
  · exfalso
    have hg : good p (2*L) := by
      rcases negative_prefix_or_return p P r a y L hodd hy hU (by simpa [r,H] using hV) hsep with h|h
      · exact False.elim (hex h)
      · exact h
    have hav : avoid p (2*L) := by
      intro k hk hkN hs
      exact hex ⟨k,trace p k,hk,hkN,hg k hkN,hs⟩
    obtain ⟨_,e,hb⟩ := tracePhasePrefix p L (2*L) hodd hg hav (by omega)
    let U := fun i => Uc (trace p (2*i))
    let V := fun i => Vc (trace p (2*i))
    let ph := fun i => phaseOf (trace p (2*i))
    have hU' : U 0=a*P := by simpa [U,trace,run] using hU
    have hV' : V 0=r*P+y := by simpa [V,trace,run,r,H] using hV
    have hphys : Physical U V L := by intro j hj; simp [U,V,Uc,Vc]; omega
    have hB := leading_bounds P r a 0 y L L U V e (by decide) (by omega) (by omega)
      (by simpa using hU') hV' (phase_blocks_weaken U V e ph L hb) hphys hsep
    have hH : 0<H := by dsimp [H]; exact Int.pow_pos (by decide)
    have hr : r=54*H := rfl
    have hZ : lead r a e I=H*(a-108*word4 e I) := by
      rw [lead_word4]
      dsimp [r,H]
      grind +ring
    have h := four_scaled54 H r a e I (a-108*word4 e I) hH hr hZ
      (by simpa [L] using hB)
    rcases h with h|h|h|h
    · rw [h,Int.mul_zero] at hZ
      have he := negative_error P r a y L U V e ph hy hU' hV' hb I
        (by dsimp [L]; omega)
      have hp := hphys I (by dsimp [L]; omega)
      rw [hZ,Int.zero_mul,Int.sub_zero] at he
      omega
    · have : False := by omega
      exact this.elim
    · have : False := by omega
      exact this.elim
    · exact hres e (by omega)

theorem d234_even_resonance_mod9 (m I : Nat) (e : Nat → Bool)
    (h : (2496:Int)*m+23808 = 36+108*word4 e I) :
    m%9=8 := by
  have hw := word4_bound e I
  omega

theorem d234_even_resonance_word (q I : Nat) (e : Nat → Bool)
    (h : (2496:Int)*(9*q+8)+23808 = 36+108*word4 e I) :
    word4 e I = 208*q+405 := by
  omega

theorem d234_even_nonresonant_mod9 (m I : Nat) (hm : m%9≠8) :
    ∀ e : Nat → Bool,
      (2496:Int)*m+23808 ≠ 36+108*word4 e I := by
  intro e h
  exact hm (d234_even_resonance_mod9 m I e h)

#print axioms four_scaled54
#print axioms return_from_exact_burst_even
#print axioms d234_even_resonance_mod9
#print axioms d234_even_resonance_word
#print axioms d234_even_nonresonant_mod9

end BB429.CoarseExit
