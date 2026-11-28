import BB429Resonance234Return
import BB429ResonanceEven

namespace BB429.CoarseExit

set_option maxHeartbeats 50000000

/-- The doubled d=234 burst has no infinite resonant escape once its physical
    scale identity is available.  If no section appears during the ordinary
    `I+4`-block leading-coefficient prefix, `four_scaled54` forces the 36
    resonance; the nonminimal-prefix package then strips it to a minimal
    suffix and the geometric tail returns to section.

    The sole finite exceptional scale m=35 is deliberately left to
    `d234_m35`, whose concrete source run is already proved separately. -/
theorem return_from_exact_burst_even_complete
    (p : State) (I m : Nat) (a P y : Int)
    (hodd : p.2%2=1) (hy : 27≤y)
    (hU : Uc p=a*P)
    (hV : Vc p=(54*(4:Int)^I)*P+y)
    (hsep : 3*cap (budget 0 y (I+4)) (I+4)+39<P)
    (hIodd : I%2=1) (hph0 : phaseOf p=true)
    (hm35 : m≠35)
    (ha : a=(2496:Int)*(m:Int)+23808)
    (hyform : y=108*(m:Int)+777-18*(I:Int))
    (hscale : (4:Int)^I*P=4*(16:Int)^m) :
    ∃ k t, 0<k ∧ k≤2*I+4*m+8 ∧ run k p=some t ∧ isSection t := by
  classical
  let L := I+4
  let H : Int := (4:Int)^I
  let r : Int := 54*H
  by_cases hex : ∃ k t, 0<k ∧ k≤2*L ∧ run k p=some t ∧ isSection t
  · obtain ⟨k,t,hk,hkL,hrun,hsec⟩ := hex
    refine ⟨k,t,hk,?_,hrun,hsec⟩
    dsimp [L] at hkL
    omega
  · have hg : good p (2*L) := by
      rcases negative_prefix_or_return p P r a y L hodd hy hU
          (by simpa [r,H] using hV) hsep with h|h
      · exact False.elim (hex h)
      · exact h
    have hav : avoid p (2*L) := by
      intro k hk hkN hs
      exact hex ⟨k,trace p k,hk,hkN,hg k hkN,hs⟩
    obtain ⟨hpar,e,hb⟩ := tracePhasePrefix p L (2*L) hodd hg hav (by omega)
    let U := fun i => Uc (trace p (2*i))
    let V := fun i => Vc (trace p (2*i))
    let ph := fun i => phaseOf (trace p (2*i))
    have hU' : U 0=a*P := by
      simpa [U,trace,run] using hU
    have hV' : V 0=r*P+y := by
      simpa [V,trace,run,r,H] using hV
    have hphys : Physical U V L := by
      intro j hj
      simp [U,V,Uc,Vc]
      omega
    have hB := leading_bounds P r a 0 y L L U V e (by decide) (by omega) (by omega)
      (by simpa using hU') hV' (phase_blocks_weaken U V e ph L hb) hphys hsep
    have hH : 0<H := by
      dsimp [H]
      exact Int.pow_pos (by decide)
    have hr : r=54*H := rfl
    have hZ : lead r a e I=H*(a-108*word4 e I) := by
      rw [lead_word4]
      dsimp [r,H]
      grind +ring
    have hforced := four_scaled54 H r a e I (a-108*word4 e I) hH hr hZ
      (by simpa [L] using hB)
    have hres : a=36+108*word4 e I := by
      rcases hforced with hzero|h36
      · rw [hzero,Int.mul_zero] at hZ
        have he := negative_error P r a y L U V e ph hy hU' hV' hb I
          (by dsimp [L]; omega)
        have hp := hphys I (by dsimp [L]; omega)
        rw [hZ,Int.zero_mul,Int.sub_zero] at he
        omega
      · omega
    have hresfixed :
        (2496:Int)*(m:Int)+23808=36+108*word4 e I := by
      rw [←ha]
      exact hres
    have hbI : PhaseBlocks U V e ph I := by
      intro j hj
      exact hb j (by dsimp [L]; omega)
    have hstart : ph 0=decide (I%2=1) := by
      simpa [ph,trace,run,hIodd] using hph0
    have hphI : ph I=false := phaseBlocks_end_false U V e ph I hbI hstart
    have hoddI : (trace p (2*I)).2%2=1 := hpar I (by dsimp [L]; omega)
    have hUfixed : U 0=((2496:Int)*(m:Int)+23808)*P := by
      rw [←ha]
      exact hU'
    have hVfixed :
        V 0=(54*(4:Int)^I)*P+(108*(m:Int)+777-18*(I:Int)) := by
      rw [hyform]
      simpa [r,H] using hV'
    have htail := d234_resonant_endpoint_evacuates
      I m L P U V e ph (trace p (2*I)).1 (trace p (2*I)).2
      (by dsimp [L]; omega) hm35 hresfixed hUfixed hVfixed hb
      (by simp [U]) (by simp [V]) hscale hoddI (by simpa [ph] using hphI)
    obtain ⟨i,J,C,hi7,hiI,hgap,hJdef,hret,hsec⟩ := htail
    have hpre := hg (2*I) (by dsimp [L]; omega)
    have hrun : run (2*I+(4*J+4)) p=some (11,C+13) := by
      rw [run_add,hpre]
      simp only [Option.bind_some]
      simpa only [Prod.eta] using hret
    refine ⟨2*I+(4*J+4),(11,C+13),by omega,?_,hrun,hsec⟩
    have hJm : J≤m := by omega
    omega

#print axioms return_from_exact_burst_even_complete

end BB429.CoarseExit
