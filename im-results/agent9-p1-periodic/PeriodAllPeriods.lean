import PeriodFactorization
import PeriodMarkerMinimal
import PeriodPrimitive

namespace PeriodWord

open PeriodPrimitive

/-- Any infinite fixed-word scalar inverse ray with positive depth has an
    integral block slope. The minimal marker return is therefore defined. -/
theorem no_infinite_positive_depth_periodic_ray (L : Nat) (w : List Nat)
    (hp : ∃ t ∈ w, 0<t) (m z : Nat → Nat)
    (hr : ∀ n, Run L w (m n) (z n) (m (n+1)) (z (n+1))) : False := by
  have hS : 1<cost w := positive_depth_cost w hp
  have hH : 0<weight w ∧ weight w<2^(cost w)-1 := positive_marker w hp
  have hSpos : 0<cost w := by omega
  have hSlope := periodic_run_slope_at_zero L w hSpos m z hr
  have hpowcast : (2:Int)^(cost w)=((2^(cost w):Nat):Int) := by
    change ((2:Nat):Int)^(cost w)=((2^(cost w):Nat):Int)
    rw [← Int.natCast_pow]
  have hSlopeCast :
      (((2^(cost w):Nat):Int)-1)*((z 1:Int)-(z 0:Int)) =
        (weight w:Int)*(cost w:Int) := by
    simpa only [hpowcast] using hSlope
  let Q : Nat := z 1-z 0
  have hQintPos : 0<((z 1:Int)-(z 0:Int)) := by
    have hBpos : 0<((2^(cost w):Nat):Int)-1 := by
      have hpw : 1<2^(cost w) := Nat.one_lt_two_pow (Nat.ne_of_gt hSpos)
      exact Int.sub_pos.mpr (by exact_mod_cast hpw)
    have hHSpos : 0<(weight w:Int)*(cost w:Int) := by
      exact_mod_cast Nat.mul_pos hH.1 hSpos
    by_cases hQnonpos : ((z 1:Int)-(z 0:Int))≤0
    · have hprodle :
          (((2^(cost w):Nat):Int)-1)*((z 1:Int)-(z 0:Int))≤0 :=
        Int.mul_nonpos_of_nonneg_of_nonpos (by omega) hQnonpos
      rw [hSlopeCast] at hprodle
      omega
    · omega
  have hle : z 0≤z 1 := by
    by_cases h : z 0≤z 1
    · exact h
    · have hlt : z 1<z 0 := by omega
      have hneg : (z 1:Int)-(z 0:Int)<0 :=
        Int.sub_neg_of_lt (by exact_mod_cast hlt)
      omega
  have hQcast : (Q:Int)=((z 1:Int)-(z 0:Int)) := by
    dsimp [Q]
    exact Int.natCast_sub hle
  have hQpos : 0<Q := by
    have hQi : 0<(Q:Int) := by rw [hQcast]; exact hQintPos
    exact_mod_cast hQi
  have hBcast : ((2^(cost w)-1:Nat):Int)=
      ((2^(cost w):Nat):Int)-1 := by
    have hh : 1≤2^(cost w) := Nat.one_le_pow (cost w) 2 (by decide)
    omega
  have hratio : (2^(cost w)-1)*Q=cost w*weight w := by
    have hI : ((2^(cost w)-1:Nat):Int)*(Q:Int)=
        ((cost w*weight w:Nat):Int) := by
      rw [hBcast,hQcast]
      simpa [Int.mul_comm] using hSlope
    exact_mod_cast hI
  have hBpos : 0<2^(cost w)-1 := by
    have hpw : 1<2^(cost w) := Nat.one_lt_two_pow (Nat.ne_of_gt hSpos)
    omega
  have hQlt : Q<cost w := by
    have hmul :
        (2^(cost w)-1)*Q < (2^(cost w)-1)*cost w := by
      calc
        (2^(cost w)-1)*Q = cost w*weight w := hratio
        _ < cost w*(2^(cost w)-1) :=
          Nat.mul_lt_mul_of_pos_left hH.2 hSpos
        _ = (2^(cost w)-1)*cost w := by ac_rfl
    exact (Nat.mul_lt_mul_left hBpos).mp hmul
  rcases PeriodMarker.shorter_marker_rotation_minimal
      (cost w) (weight w) Q hS hH ⟨hQpos,hQlt⟩ hratio with
    ⟨d,hdpos,hdlt,hdvd,hrot,hminimal⟩
  rcases factor_word_of_rotation_period w d hdpos hdlt hdvd hH.2 hrot with
    ⟨u,k,hkpos,hcostU,hweightUlt,hfactor⟩
  have hcostW : cost w=d*k := by
    calc
      cost w=cost (repeatWord u k) := by rw [hfactor]
      _=cost u*k := cost_repeat u k
      _=d*k := by rw [hcostU]
  have hWrep : weight w=weight u*geomN (2^d) k := by
    rw [hfactor,weight_repeat,hcostU]
  have hBrep : 2^(cost w)-1=(2^d-1)*geomN (2^d) k := by
    calc
      2^(cost w)-1=2^(d*k)-1 := by rw [hcostW]
      _=(2^d)^k-1 := by rw [Nat.pow_mul]
      _=(2^d-1)*geomN (2^d) k :=
        (geomN_identity (2^d) k (Nat.pow_pos (by decide : 0<2))).symm
  have hprim : PeriodPrimitive.Primitive u := by
    intro s hspos hslt hrotU
    let J : Nat := geomN (2^d) k
    let q : Nat := (2^s*weight u)/(2^d-1)
    have hdecomp : 2^s*weight u=weight u+(2^d-1)*q := by
      have h := Nat.mod_add_div (2^s*weight u) (2^d-1)
      rw [hrotU] at h
      change weight u+(2^d-1)*q=2^s*weight u at h
      exact h.symm
    have hWrep' : weight w=weight u*J := by simpa [J] using hWrep
    have hBrep' : 2^(cost w)-1=(2^d-1)*J := by simpa [J] using hBrep
    have hLift : 2^s*weight w=weight w+(2^(cost w)-1)*q := by
      rw [hWrep',hBrep']
      calc
        2^s*(weight u*J)=(2^s*weight u)*J := by ac_rfl
        _=(weight u+(2^d-1)*q)*J := by rw [hdecomp]
        _=weight u*J+(2^d-1)*J*q := by rw [Nat.add_mul]; ac_rfl
    have hrotW : (2^s*weight w)%(2^(cost w)-1)=weight w := by
      calc
        (2^s*weight w)%(2^(cost w)-1)=
            (weight w+(2^(cost w)-1)*q)%(2^(cost w)-1) := by rw [hLift]
        _=weight w%(2^(cost w)-1) :=
            Nat.add_mul_mod_self_left _ _ _
        _=weight w := Nat.mod_eq_of_lt hH.2
    exact hminimal s hspos (by simpa [hcostU] using hslt) hrotW
  have hpU : ∃ t ∈ u, 0<t := by
    have hnot : ¬ ∀ t ∈ u, t=0 := by
      intro hall
      have hloss : loss u=0 := (loss_zero_iff u).2 hall
      have hc := cost_weight_loss u
      rw [hloss,hcostU] at hc
      omega
    obtain ⟨t,ht⟩ := Classical.not_forall.mp hnot
    simp only [not_imp] at ht
    rcases ht with ⟨htmem,htnz⟩
    exact ⟨t,htmem,by omega⟩
  have hr' : ∀ n, Run L (repeatWord u k) (m n) (z n) (m (n+1)) (z (n+1)) := by
    intro n
    rw [←hfactor]
    exact hr n
  exact no_infinite_repeated_word_ray L u k hkpos hpU hprim m z hr'

#print axioms no_infinite_positive_depth_periodic_ray

end PeriodWord
