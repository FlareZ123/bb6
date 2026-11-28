import BB429Resonance234Evacuation

namespace BB429.CoarseExit

open BB429.LowReturnBand

set_option maxHeartbeats 30000000

theorem d234_resonant_endpoint_evacuates
    (I m n : Nat) (P : Int)
    (U V : Nat → Int) (e ph : Nat → Bool) (u w : Nat)
    (hIn : I≤n) (hm35 : m≠35)
    (hres : (2496:Int)*(m:Int)+23808 = 36+108*word4 e I)
    (hU0 : U 0=((2496:Int)*(m:Int)+23808)*P)
    (hV0 : V 0=(54*(4:Int)^I)*P+(108*(m:Int)+777-18*(I:Int)))
    (hs : PhaseBlocks U V e ph n)
    (hUI : U I=Uc (u,w)) (hVI : V I=Vc (u,w))
    (hscale : (4:Int)^I*P=4*(16:Int)^m)
    (hodd : w%2=1) (hph : phaseOf (u,w)=false) :
    ∃ i J C : Nat, 7≤i ∧ i≤I ∧ 5*i+61≤m ∧ J=m-i+1 ∧
      run (4*J+4) (u,w)=some (11,C+13) ∧ isSection (11,C+13) := by
  obtain ⟨i,hi7,hiI,hgap,hz0,hzhi,hlo,hhi⟩ :=
    d234_resonant_endpoint_package I m n P U V e ph hIn hm35 hres hU0 hV0 hs
  let x : Int := U I-(36*(4:Int)^I)*P
  let z : Int := V I-(54*(4:Int)^I)*P
  have hUphys : Uc (u,w)=144*(16^m:Int)+x := by
    dsimp [x]
    rw [←hUI]
    have hs36 : (36:Int)*((4:Int)^I*P)=144*(16:Int)^m := by
      rw [hscale]
      grind +ring
    grind +ring
  have hVphys : Vc (u,w)=216*(16^m:Int)+z := by
    dsimp [z]
    rw [←hVI]
    have hs54 : (54:Int)*((4:Int)^I*P)=216*(16:Int)^m := by
      rw [hscale]
      grind +ring
    grind +ring
  change 0≤z at hz0
  change z≤108*(m:Int)+777+24*(i:Int) at hzhi
  change 54*(4:Int)^i*(4:Int)^i < 16*(-6*x+4*z+12) at hlo
  change 4*(-6*x+4*z+12)≤27*(4:Int)^i*(4:Int)^i at hhi
  obtain ⟨q,d,J,X,C,hzq,hwd,hJdef,hXdef,hC,hdu,hmod,hDhi,hClo,hChi,hClow⟩ :=
    d234_endpoint_evacuation_data m i u w x z hi7 hgap hUphys hVphys hz0 hzhi hlo hhi hodd hph
  have hJ : 1≤J := by omega
  have hm1 : 1≤m := by omega
  have hpow : 16^1≤16^m := Nat.pow_le_pow_right (by decide) hm1
  have hX2 : 2≤X := by rw [hXdef]; omega
  have hret := false_resonance_evacuation u d J X C hmod hdu hJ hX2 hC hDhi hClo hChi hClow
  have hstate : (u,w)=phase u d := by simp [phase,hwd]
  rw [←hstate] at hret
  refine ⟨i,J,C,hi7,hiI,hgap,hJdef,hret,?_⟩
  simp [isSection]

#print axioms d234_resonant_endpoint_evacuates

end BB429.CoarseExit
