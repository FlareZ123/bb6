import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 100000
set_option maxRecDepth 8192

namespace BB6.Agent3U5Q0H8Residue

private theorem residual_rhs_div8192 (w : Nat) :
    8192 ∣ 20 * 2 ^ (201 + 3360 * w) := by
  have hdiv : 8192 ∣ 2 ^ (201 + 3360 * w) := by
    change 2 ^ 13 ∣ 2 ^ (201 + 3360 * w)
    exact Nat.pow_dvd_pow 2 (by omega)
  rcases hdiv with ⟨q, hq⟩
  refine ⟨20 * q, ?_⟩
  rw [hq]
  omega

private theorem residual_linear_div8192 (w t : Nat)
    (hres : 211 * t + 1360 + 22155 * w =
      20 * 2 ^ (201 + 3360 * w)) :
    8192 ∣ 211 * t + 1360 + 22155 * w := by
  rw [hres]
  exact residual_rhs_div8192 w

private theorem solve_t_mod8192 (t : Nat)
    (hdiv : 8192 ∣ 211 * t + 147487195) : t % 8192 = 551 := by
  rcases hdiv with ⟨m, hm⟩
  have hcoeff : 5979 * 211 = 1 + 8192 * 154 := by decide
  have hconst : 5979 * 147487195 = 7641 + 8192 * 107644767 := by decide
  have hmul : 8192 ∣ 5979 * (211 * t + 147487195) := by
    refine ⟨5979 * m, ?_⟩
    rw [hm]
    omega
  have hexpand :
      5979 * (211 * t + 147487195) =
        (t + 7641) + 8192 * (154 * t + 107644767) := by
    calc
      5979 * (211 * t + 147487195) = 5979 * (211 * t) + 5979 * 147487195 := by rw [Nat.mul_add]
      _ = (5979 * 211) * t + 5979 * 147487195 := by rw [Nat.mul_assoc]
      _ = (1 + 8192 * 154) * t + (7641 + 8192 * 107644767) := by rw [hcoeff, hconst]
      _ = (t + 7641) + 8192 * (154 * t + 107644767) := by omega
  have hB : 8192 ∣ 8192 * (154 * t + 107644767) :=
    ⟨154 * t + 107644767, rfl⟩
  have hsumdiv : 8192 ∣ (t + 7641) + 8192 * (154 * t + 107644767) := by
    rw [hexpand] at hmul
    exact hmul
  have hdivA : 8192 ∣ t + 7641 :=
    (Nat.dvd_add_iff_left hB).mpr hsumdiv
  have hdecomp : t + 7641 = (t % 8192 + 7641) + 8192 * (t / 8192) := by
    have h := Nat.mod_add_div t 8192
    omega
  have hB' : 8192 ∣ 8192 * (t / 8192) := ⟨t / 8192, rfl⟩
  have hsumdiv' : 8192 ∣ (t % 8192 + 7641) + 8192 * (t / 8192) := by
    rw [← hdecomp]
    exact hdivA
  have hremdiv : 8192 ∣ t % 8192 + 7641 :=
    (Nat.dvd_add_iff_left hB').mpr hsumdiv'
  rcases hremdiv with ⟨q, hq⟩
  have htlt : t % 8192 < 8192 := Nat.mod_lt _ (by decide)
  have hqone : q = 1 := by omega
  omega

private theorem solve_w_mod8192 (w : Nat)
    (hdiv : 8192 ∣ 117621 + 22155 * w) : w % 8192 = 6657 := by
  rcases hdiv with ⟨m, hm⟩
  have hcoeff : 291 * 22155 = 1 + 8192 * 787 := by decide
  have hconst : 291 * 117621 = 1535 + 8192 * 4178 := by decide
  have hmul : 8192 ∣ 291 * (117621 + 22155 * w) := by
    refine ⟨291 * m, ?_⟩
    rw [hm]
    omega
  have hexpand :
      291 * (117621 + 22155 * w) =
        (w + 1535) + 8192 * (787 * w + 4178) := by
    calc
      291 * (117621 + 22155 * w) = 291 * 117621 + 291 * (22155 * w) := by rw [Nat.mul_add]
      _ = 291 * 117621 + (291 * 22155) * w := by rw [Nat.mul_assoc]
      _ = (1535 + 8192 * 4178) + (1 + 8192 * 787) * w := by rw [hcoeff, hconst]
      _ = (w + 1535) + 8192 * (787 * w + 4178) := by omega
  have hB : 8192 ∣ 8192 * (787 * w + 4178) :=
    ⟨787 * w + 4178, rfl⟩
  have hsumdiv : 8192 ∣ (w + 1535) + 8192 * (787 * w + 4178) := by
    rw [hexpand] at hmul
    exact hmul
  have hdivA : 8192 ∣ w + 1535 :=
    (Nat.dvd_add_iff_left hB).mpr hsumdiv
  have hdecomp : w + 1535 = (w % 8192 + 1535) + 8192 * (w / 8192) := by
    have h := Nat.mod_add_div w 8192
    omega
  have hB' : 8192 ∣ 8192 * (w / 8192) := ⟨w / 8192, rfl⟩
  have hsumdiv' : 8192 ∣ (w % 8192 + 1535) + 8192 * (w / 8192) := by
    rw [← hdecomp]
    exact hdivA
  have hremdiv : 8192 ∣ w % 8192 + 1535 :=
    (Nat.dvd_add_iff_left hB').mpr hsumdiv'
  rcases hremdiv with ⟨q, hq⟩
  have hwlt : w % 8192 < 8192 := Nat.mod_lt _ (by decide)
  have hqone : q = 1 := by omega
  omega

/-- The residual identity fixes t modulo 8192 whenever w=6657 mod 8192. -/
theorem residual_t_mod8192_of_w (w t : Nat)
    (hres : 211 * t + 1360 + 22155 * w =
      20 * 2 ^ (201 + 3360 * w))
    (hw : w % 8192 = 6657) : t % 8192 = 551 := by
  have hlin := residual_linear_div8192 w t hres
  have hwdecomp : w = 8192 * (w / 8192) + 6657 := by
    have h := Nat.mod_add_div w 8192
    omega
  rw [hwdecomp] at hlin
  have hsumEq :
      211 * t + 1360 + 22155 * (8192 * (w / 8192) + 6657) =
        (211 * t + 147487195) + 8192 * (22155 * (w / 8192)) := by omega
  have hdivSimple : 8192 ∣ (211 * t + 147487195) + 8192 * (22155 * (w / 8192)) := by
    rw [hsumEq] at hlin
    exact hlin
  have hB : 8192 ∣ 8192 * (22155 * (w / 8192)) :=
    ⟨22155 * (w / 8192), rfl⟩
  have hdivA : 8192 ∣ 211 * t + 147487195 :=
    (Nat.dvd_add_iff_left hB).mpr hdivSimple
  exact solve_t_mod8192 t hdivA

/-- Conversely, the residual identity and t=551 mod 8192 force w=6657 mod 8192. -/
theorem residual_w_mod8192_of_t (w t : Nat)
    (hres : 211 * t + 1360 + 22155 * w =
      20 * 2 ^ (201 + 3360 * w))
    (ht : t % 8192 = 551) : w % 8192 = 6657 := by
  have hlin := residual_linear_div8192 w t hres
  have htdecomp : t = 8192 * (t / 8192) + 551 := by
    calc
      t = t % 8192 + 8192 * (t / 8192) := (Nat.mod_add_div t 8192).symm
      _ = 551 + 8192 * (t / 8192) := by rw [ht]
      _ = 8192 * (t / 8192) + 551 := Nat.add_comm _ _
  rw [htdecomp] at hlin
  have hsumEq :
      211 * (8192 * (t / 8192) + 551) + 1360 + 22155 * w =
        (117621 + 22155 * w) + 8192 * (211 * (t / 8192)) := by omega
  have hdivSimple : 8192 ∣ (117621 + 22155 * w) + 8192 * (211 * (t / 8192)) := by
    rw [hsumEq] at hlin
    exact hlin
  have hB : 8192 ∣ 8192 * (211 * (t / 8192)) :=
    ⟨211 * (t / 8192), rfl⟩
  have hdivA : 8192 ∣ 117621 + 22155 * w :=
    (Nat.dvd_add_iff_left hB).mpr hdivSimple
  exact solve_w_mod8192 w hdivA

/-- The U5 q=0 parameter h=8 mod 128 is exactly the root cylinder
w=6657 mod 8192 under the authentic residual identity. -/
theorem residual_h8_iff_w6657 (w h : Nat)
    (hres : 211 * (39 + 64 * h) + 1360 + 22155 * w =
      20 * 2 ^ (201 + 3360 * w)) :
    h % 128 = 8 ↔ w % 8192 = 6657 := by
  constructor
  · intro hh
    have hhdecomp : h = 128 * (h / 128) + 8 := by
      calc
        h = h % 128 + 128 * (h / 128) := (Nat.mod_add_div h 128).symm
        _ = 8 + 128 * (h / 128) := by rw [hh]
        _ = 128 * (h / 128) + 8 := Nat.add_comm _ _
    have h64128 : 64 * 128 = 8192 := by decide
    have h648 : 64 * 8 = 512 := by decide
    have htform : 39 + 64 * h = 8192 * (h / 128) + 551 := by
      have harg := congrArg (fun z : Nat => 39 + 64 * z) hhdecomp
      calc
        39 + 64 * h = 39 + 64 * (128 * (h / 128) + 8) := harg
        _ = 39 + (8192 * (h / 128) + 512) := by
          have hmul : 64 * (128 * (h / 128)) = 8192 * (h / 128) := by
            calc
              64 * (128 * (h / 128)) = (64 * 128) * (h / 128) :=
                (Nat.mul_assoc 64 128 (h / 128)).symm
              _ = 8192 * (h / 128) := by rw [h64128]
          rw [Nat.mul_add, hmul, h648]
        _ = 8192 * (h / 128) + 551 := by
          calc
            39 + (8192 * (h / 128) + 512) =
                (39 + 8192 * (h / 128)) + 512 := (Nat.add_assoc _ _ _).symm
            _ = (8192 * (h / 128) + 39) + 512 := by
              rw [Nat.add_comm 39 (8192 * (h / 128))]
            _ = 8192 * (h / 128) + (39 + 512) := Nat.add_assoc _ _ _
            _ = 8192 * (h / 128) + 551 := by rw [show 39 + 512 = 551 by decide]
    have ht : (39 + 64 * h) % 8192 = 551 := by
      rw [htform]
      simp
    exact residual_w_mod8192_of_t w (39 + 64 * h) hres ht
  · intro hw
    have ht := residual_t_mod8192_of_w w (39 + 64 * h) hres hw
    have htdiv : 39 + 64 * h = 8192 * ((39 + 64 * h) / 8192) + 551 := by
      calc
        39 + 64 * h = (39 + 64 * h) % 8192 + 8192 * ((39 + 64 * h) / 8192) :=
          (Nat.mod_add_div (39 + 64 * h) 8192).symm
        _ = 551 + 8192 * ((39 + 64 * h) / 8192) := by rw [ht]
        _ = 8192 * ((39 + 64 * h) / 8192) + 551 := Nat.add_comm _ _
    have h64128 : 64 * 128 = 8192 := by decide
    have h648 : 64 * 8 = 512 := by decide
    let q := (39 + 64 * h) / 8192
    have htdivq : 39 + 64 * h = 8192 * q + 551 := by
      change 39 + 64 * h = 8192 * ((39 + 64 * h) / 8192) + 551
      exact htdiv
    have hshift : 8192 * q + 551 = 39 + (8192 * q + 512) := by
      calc
        8192 * q + 551 = 8192 * q + (39 + 512) := by rw [show 551 = 39 + 512 by decide]
        _ = (8192 * q + 39) + 512 := (Nat.add_assoc _ _ _).symm
        _ = (39 + 8192 * q) + 512 := by rw [Nat.add_comm (8192 * q) 39]
        _ = 39 + (8192 * q + 512) := Nat.add_assoc _ _ _
    have hsum : 39 + 64 * h = 39 + (8192 * q + 512) := htdivq.trans hshift
    have heq1 : 64 * h = 8192 * q + 512 := Nat.add_left_cancel hsum
    have hmul : 64 * (128 * q) = 8192 * q := by
      calc
        64 * (128 * q) = (64 * 128) * q := (Nat.mul_assoc 64 128 q).symm
        _ = 8192 * q := by rw [h64128]
    have heq2 : 64 * (128 * q + 8) = 8192 * q + 512 := by
      rw [Nat.mul_add, hmul, h648]
    have heq : 64 * h = 64 * (128 * q + 8) := heq1.trans heq2.symm
    have hform : h = 128 * q + 8 :=
      Nat.mul_left_cancel (by decide : 0 < 64) heq
    rw [hform]
    simp

#print axioms residual_t_mod8192_of_w
#print axioms residual_w_mod8192_of_t
#print axioms residual_h8_iff_w6657

end BB6.Agent3U5Q0H8Residue
