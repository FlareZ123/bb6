import BB429Resonance234Close
import BB429ResonancePhysical

namespace BB429.CoarseExit

set_option maxRecDepth 20000
set_option maxHeartbeats 30000000

theorem d234_endpoint_evacuation_data
    (m i u w : Nat) (x z : Int)
    (hi7 : 7≤i) (hgap : 5*i+61≤m)
    (hU : Uc (u,w)=144*(16^m:Int)+x)
    (hV : Vc (u,w)=216*(16^m:Int)+z)
    (hz0 : 0≤z)
    (hzhi : z≤108*(m:Int)+777+24*(i:Int))
    (hbandlo : 54*(4:Int)^i*(4:Int)^i < 16*(-6*x+4*z+12))
    (hbandhi : 4*(-6*x+4*z+12)≤27*(4:Int)^i*(4:Int)^i)
    (hodd : w%2=1) (hph : phaseOf (u,w)=false) :
    ∃ q d J X C : Nat,
      z=3*(q:Int) ∧
      w=u+12+d ∧
      J=m-i+1 ∧ X=16^m ∧ C=3*(u-d-2)+(4*d+16)+24*J ∧
      d+17≤u ∧ (u-d)%4=1 ∧
      (4*d+16)*16^J≤36*X ∧
      72*X≤C ∧
      C≤4*((4*d+16)*16^J)+27 ∧
      8*((4*d+16)*16^J)+21≤5*C := by
  have hzmod : z%3=0 := by
    simp [Vc] at hV
    omega
  have hdvd : (3:Int) ∣ z := Int.dvd_of_emod_eq_zero hzmod
  obtain ⟨qI,hzqI⟩ := hdvd
  have hqI0 : 0≤qI := by
    rw [hzqI] at hz0
    omega
  let q : Nat := qI.toNat
  have hqcast : (q:Int)=qI := by
    dsimp [q]
    exact Int.toNat_of_nonneg hqI0
  have hzq : z=3*(q:Int) := by
    rw [hqcast]
    exact hzqI
  have hqhiI : qI≤36*(m:Int)+259+8*(i:Int) := by
    rw [hzqI] at hzhi
    omega
  have hH4N : 4^1≤4^i := Nat.pow_le_pow_right (by decide) (by omega)
  have hH4 : (4:Int)≤(4:Int)^i := by
    exact_mod_cast hH4N
  have hH0 : (0:Int)≤(4:Int)^i := Int.pow_nonneg (by decide)
  have hsq1 : (16:Int)≤(4:Int)^i*4 := by
    have h := Int.mul_le_mul_of_nonneg_right hH4 (by decide : (0:Int)≤4)
    omega
  have hsq : (16:Int)≤(4:Int)^i*(4:Int)^i := by
    have h := Int.mul_le_mul_of_nonneg_left hH4 hH0
    omega
  have hdc48 : 48≤-6*x+4*z+12 := by
    have hmul0 := Int.mul_le_mul_of_nonneg_left hsq (by decide : (0:Int)≤54)
    have hmul : (864:Int)≤54*(4:Int)^i*(4:Int)^i := by
      calc
        (864:Int) = 54*16 := by decide
        _ ≤ 54*((4:Int)^i*(4:Int)^i) := hmul0
        _ = 54*(4:Int)^i*(4:Int)^i := by grind +ring
    omega
  have hphys := resonance_error_physical u w (16^m) x qI hU
    (by rw [hzqI] at hV; simpa [Int.mul_assoc] using hV)
    (by rw [hzqI] at hdc48; omega)
  obtain ⟨d,hwd,hdc,hinv⟩ := hphys
  let H : Int := (4:Int)^i
  let J : Nat := m-i+1
  let N : Int := (16:Int)^(m-i)
  let X : Int := (16:Int)^m
  let d0 : Int := 4*(d:Int)+16
  let D : Int := 16*d0*N
  let C : Int := 72*X+qI-2+24*(J:Int)
  have hJ : 1≤J := by dsimp [J]; omega
  have hN : 1≤N := by
    dsimp [N]
    have h := Int.pow_pos (m:=m-i) (show (0:Int)<16 by decide)
    omega
  have hXpos : 1≤X := by
    dsimp [X]
    have h := Int.pow_pos (m:=m) (show (0:Int)<16 by decide)
    omega
  have h16 : (16:Int)^i=(4:Int)^i*(4:Int)^i := by
    rw [←Int.mul_pow]
    congr 2
  have hX : X=H*H*N := by
    dsimp [X,H,N]
    calc
      (16:Int)^m = (16:Int)^(i+(m-i)) := by congr 2 <;> omega
      _ = (16:Int)^i*(16:Int)^(m-i) := by rw [Int.pow_add]
      _ = (4:Int)^i*(4:Int)^i*(16:Int)^(m-i) := by rw [h16]
  have hdc' : (3:Int)*(4*(d:Int)+16)=-6*x+4*z+12 := by
    rw [hzqI]
    omega
  have hlo : 18*H*H<16*d0 := by
    have hb := hbandlo
    rw [←hdc'] at hb
    have hb' : 3*(18*H*H)<3*(16*d0) := by
      calc
        3*(18*H*H) = 54*H*H := by grind +ring
        _ < 16*(3*d0) := by simpa [H,d0] using hb
        _ = 3*(16*d0) := by grind +ring
    omega
  have hhi : 4*d0≤9*H*H := by
    have hb := hbandhi
    rw [←hdc'] at hb
    have hb' : 3*(4*d0)≤3*(9*H*H) := by
      calc
        3*(4*d0) = 4*(3*d0) := by grind +ring
        _ ≤ 27*H*H := by simpa [H,d0] using hb
        _ = 3*(9*H*H) := by grind +ring
    omega
  have hmarginN := d234_margin_growth i m hgap
  have hmargin : 60*(m:Int)+254≤16*(i:Int)+4*N := by
    dsimp [N]
    exact_mod_cast hmarginN
  have hs := d234_scalar_window_arith i m J H N X d0 D C qI
    (by rfl) hJ hN hXpos hX (by rfl) hlo hhi hqI0 hqhiI (by rfl) hmargin
  let XN : Nat := 16^m
  have hXcast : (XN:Int)=X := by simp [XN,X]
  have hpowJ : (16:Int)^J=16*N := by
    dsimp [J,N]
    rw [show m-i+1=(m-i)+1 by omega,Int.pow_succ]
    grind +ring
  have hDcast : (((4*d+16)*16^J:Nat):Int)=D := by
    dsimp [D,d0]
    push_cast
    rw [hpowJ]
    grind +ring
  have hDhiI := hs.1
  rw [←hDcast,←hXcast] at hDhiI
  have hDhiN : (4*d+16)*16^J≤36*XN := by
    exact_mod_cast hDhiI
  have hD16 : 16*(4*d+16)≤36*XN := by
    have hp : 16≤16^J := by
      rw [show J=(J-1)+1 by omega,Nat.pow_succ]
      have hpos : 1≤16^(J-1) := Nat.pow_pos (by decide)
      omega
    have hm := Nat.mul_le_mul_left (4*d+16) hp
    omega
  have hD16I : (16:Int)*(4*(d:Int)+16)≤36*(XN:Int) := by
    exact_mod_cast hD16
  have hdu17 : d+17≤u := by
    have hx : (XN:Int)=(16:Int)^m := by simp [XN]
    rw [hx] at hD16I
    omega
  let CN : Nat := 3*(u-d-2)+(4*d+16)+24*J
  have hCcast : (CN:Int)=C := by
    have hdu : d≤u := by omega
    have hsub2 : 2≤u-d := by omega
    dsimp [CN,C]
    rw [Int.natCast_sub hsub2,Int.natCast_sub hdu]
    rw [←hXcast,←hqcast]
    omega
  have hrest := hs.2
  rw [←hDcast,←hXcast,←hCcast] at hrest
  have hCloN : 72*XN≤CN := by
    exact_mod_cast hrest.1
  have hChiN : CN≤4*((4*d+16)*16^J)+27 := by
    exact_mod_cast hrest.2.1
  have hClowN : 8*((4*d+16)*16^J)+21≤5*CN := by
    exact_mod_cast hrest.2.2
  have hmod := false_phase_rotation_mod u w d hodd hph hwd (by omega)
  refine ⟨q,d,J,XN,CN,hzq,hwd,rfl,rfl,rfl,hdu17,hmod,hDhiN,hCloN,hChiN,hClowN⟩

#print axioms d234_endpoint_evacuation_data

end BB429.CoarseExit
