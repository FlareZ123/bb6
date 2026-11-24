import CapModLift

namespace CapModNoGo
open CapSieve

theorem P_square {k : Nat} (hk : 4≤k) : (k+6)*(k+6)≤2*P k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : 4≤k
    · have he := ih h
      rw [p_succ]
      have hh : (k+1+6)*(k+1+6)≤2*((k+6)*(k+6)) := by
        have hmul : 0≤k*k := Nat.zero_le _
        grind
      omega
    · have he : k=3 := by omega
      subst k
      unfold P
      decide

theorem pow3_odd (r : Nat) : 3^r%2=1 := by
  induction r with
  | zero => decide
  | succ r ih => rw [Nat.pow_succ,Nat.mul_mod,ih]

/-- An exact immediate terminal preimage at any sufficiently high band
    with prescribed exact power-of-three divisor. -/
theorem immediate_terminal {k r q : Nat} (hr : 1≤r) (hk : 4≤k)
    (hsize : 3^r≤k+6) (he : 3^r*q=F k) (hu : q%3≠0) :
    CanonQ k q ∧ (signedEvent k q).2=none := by
  have hpow : 0<3^r := Nat.pow_pos (by decide)
  have hlow : k+6≤q := by
    have hsq := P_square hk
    have hm := Nat.mul_le_mul_right (k+6) hsize
    have hF : 2*P k≤F k := by unfold F; omega
    have hle : 3^r*(k+6)≤3^r*q := by omega
    exact Nat.le_of_mul_le_mul_left hle hpow
  have hr' : r-1+1=r := by omega
  have hdiv : 3^r*q=3*(3^(r-1)*q) := by
    conv => lhs; rw [←hr',Nat.pow_succ]
    ac_rfl
  have hupper : 3^(r-1)*q≤2*P k-2 := by
    have hP := p_ge k
    unfold F at he
    omega
  have hqp : q≤3^(r-1)*q :=
    Nat.le_mul_of_pos_left q (Nat.pow_pos (by decide))
  have hpar : q%2=k%2 := by
    have hh := congrArg (fun z : Nat => z%2) he
    change (3^r*q)%2=F k%2 at hh
    rw [Nat.mul_mod,pow3_odd,Nat.one_mul] at hh
    unfold F at hh
    omega
  have hc : CanonQ k q := ⟨⟨hlow,by omega,hpar⟩,Or.inl hu⟩
  have hpos : 0<q := by omega
  have hcnt : positiveCount k q=r-1 := by
    unfold positiveCount
    apply CapMacro.triple_window_unique hpos
    · exact CapMacro.tripleCount_spec hpos hc.1.2.1
    · refine ⟨hupper,?_⟩
      rw [hr',he]
      unfold F
      omega
  have hprod : positiveProduct k q=F k := by
    unfold positiveProduct
    rw [hcnt,hr',he]
  have hnext : positiveNext k q=k+3 := by
    have hn := positive_next_equation hpos hc.1.2.1
    unfold F at hprod
    omega
  refine ⟨hc,(positive_event_terminal_iff (by omega) hc.1).mpr ?_⟩
  exact ⟨0,by rw [hnext]; simp; omega⟩

/-- In a single band-index residue class, every unit coordinate residue
    is realized by arbitrarily large genuine immediate terminal states. -/
theorem terminal_residue_dense {h k0 q0 : Nat} (hh : 1≤h)
    (hk0 : F k0%3^h=0) (hq0 : q0%3≠0) (K : Nat) :
    ∃ k q, K≤k ∧ k%(2*3^h)=k0%(2*3^h) ∧ q%3^h=q0%3^h ∧
      CanonQ k q ∧ (signedEvent k q).2=none := by
  let r := h+1
  let y := 3^r*(q0%3^h)
  have hp : 0<3^h := Nat.pow_pos (by decide)
  have hR : 0<3^r := Nat.pow_pos (by decide)
  have hpow : 3^(h+r)=3^r*3^h := by rw [Nat.pow_add]; ac_rfl
  have hy : y<3^(h+r) := by
    rw [hpow]
    exact Nat.mul_lt_mul_of_pos_left (Nat.mod_lt _ hp) hR
  have hy0 : y%3^h=0 := by
    have hd : 3^h ∣ 3^r := Nat.pow_dvd_pow 3 (by dsimp [r]; omega)
    obtain ⟨c,hc⟩ := hd
    dsimp [y]
    rw [hc,Nat.mul_assoc,Nat.mul_mod_right]
  obtain ⟨k,hK,hk,hF⟩ := F_lift_unbounded h r k0 y (K+3^r+4) (hk0.trans hy0.symm)
  rw [Nat.mod_eq_of_lt hy,hpow] at hF
  let q := F k/3^r
  have hdvd : F k%3^r=0 := by
    have hh := congrArg (fun z : Nat => z%3^r) hF
    rw [Nat.mod_mod_of_dvd _ (show 3^r∣3^r*3^h from ⟨_,rfl⟩)] at hh
    dsimp [y] at hh
    rw [Nat.mul_mod_right] at hh
    exact hh
  have he : 3^r*q=F k := by
    dsimp [q]
    have := Nat.mod_add_div (F k) (3^r)
    omega
  have hq : q%3^h=q0%3^h := by
    have hh := congrArg (fun z : Nat => z/3^r) hF
    rw [Nat.mod_mul_right_div_self] at hh
    dsimp [y] at hh
    rw [Nat.mul_div_cancel_left _ hR] at hh
    exact hh
  have hu : q%3≠0 := by
    have hdiv : 3∣3^h := by
      simpa using Nat.pow_dvd_pow 3 hh
    have hm := congrArg (fun z : Nat => z%3) hq
    rw [Nat.mod_mod_of_dvd _ hdiv,Nat.mod_mod_of_dvd _ hdiv] at hm
    omega
  have hr : 1≤r := by dsimp [r]; omega
  obtain ⟨hc,ht⟩ := immediate_terminal hr (by omega) (by omega) he hu
  exact ⟨k,q,by omega,hk,hq,hc,ht⟩

/-- No eventually periodic 3-adic coordinate-only certificate with the
    same band period can cover a unit coordinate in every sufficiently
    large band while excluding all immediate halting events. -/
theorem no_periodic_barrier {h K : Nat} (hh : 1≤h)
    (I : Nat → Nat → Prop)
    (hper : ∀ k q j v, K≤k → K≤j →
      k%(2*3^h)=j%(2*3^h) → q%3^h=v%3^h → (I k q ↔ I j v))
    (hcover : ∀ k, K≤k → ∃ q, q%3≠0 ∧ I k q)
    (hsafe : ∀ k q, CanonQ k q → I k q → (signedEvent k q).2≠none) :
    False := by
  obtain ⟨k0,_,hzero⟩ := F_zero_residue h 0 (by decide)
  obtain ⟨j,hj,hjres,hjzero⟩ := F_lift_unbounded h 0 k0 0 K (by simpa using hzero)
  have hz : F j%3^h=0 := by simpa using hjzero
  obtain ⟨q0,hunit,hI⟩ := hcover j hj
  obtain ⟨k,q,hk,hkr,hqr,hc,ht⟩ := terminal_residue_dense hh hz hunit K
  have hI' := (hper j q0 k q hj hk hkr.symm hqr.symm).mp hI
  exact hsafe k q hc hI' ht

#print axioms terminal_residue_dense
#print axioms no_periodic_barrier
end CapModNoGo
