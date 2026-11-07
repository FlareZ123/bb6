import ValSixC58Late
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19HighThreeLate256

/-- The new high stopping cylinder: m is 3 modulo 256 and j is the
    explicit affine function of the stopping exponent. -/
def late256J (m : Nat) : Nat :=
  9 * 2^(2*m+2) - (3*m+3)

def late256K (j m : Nat) : Nat :=
  2^(2*m+2)*(j+3) - (j+3*m+5)

/-- Preserve the entire previously verified C58 all-depth/late predicate,
    while removing the new infinite source-excluded family. -/
def highAllowed (j m : Nat) : Prop :=
  BB6.Agent11C58Late.highAllowed j m ∧
  ¬(259≤m ∧ m%256=3 ∧ j=late256J m)

/-- The stopping equation has a useful exact sum form on this family. -/
private theorem late256_sum_identity (m : Nat) (hm : 259≤m) :
    late256J m + 3*m + 3 = 9*2^(2*m+2) := by
  have hP : 4*m+4 ≤ 2^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have hbound : 3*m+3 ≤ 9*2^(2*m+2) := by omega
  dsimp [late256J]
  exact Nat.sub_add_cancel hbound

/-- The explicit high index is 244 modulo 256 throughout the family. -/
private theorem late256_j_mod256 (m : Nat)
    (hm : 259≤m) (hmres : m%256=3) :
    late256J m % 256 = 244 := by
  let P := 2^(2*m+2)
  have hsum := late256_sum_identity m hm
  have hdiv : 256 ∣ P := by
    have h := Nat.pow_dvd_pow 2 (by omega : 8≤2*m+2)
    simpa only [show (2:Nat)^8=256 by decide, P] using h
  have hdiv9 : 256 ∣ 9*P := by
    rcases hdiv with ⟨v,hv⟩
    refine ⟨9*v,?_⟩
    rw [hv]
    ac_rfl
  have hpowmod : (9*P)%256=0 := Nat.mod_eq_zero_of_dvd hdiv9
  have hlinmod : (3*m+3)%256=12 := by omega
  have hsumAssoc : late256J m + (3*m+3)=9*P := by
    have hsum' : late256J m + 3*m+3=9*P := by simpa [P] using hsum
    omega
  have hsumMod : (late256J m + (3*m+3))%256=(9*P)%256 := by
    exact congrArg (fun z : Nat => z%256) hsumAssoc
  rw [Nat.add_mod,hpowmod,hlinmod] at hsumMod
  omega

/-- Small modular consequences of the explicit late256 residue. Keeping
    these isolated prevents Omega from normalizing the large stopping powers. -/
private theorem left_mod4_of_jmod256 (j : Nat) (hj : j%256=244) :
    (2*j+3)%4=3 := by
  have hj4 : j%4=0 := by omega
  omega

private theorem highAllowedPlus_extras_of_mod256 (j m : Nat)
    (hj : j%256=244) (hm : m%256=3) :
    ¬(4≤m ∧ j%8=5 ∧ (j+31)%128=(3*m)%128) ∧
    ¬(4≤m ∧ j%32=17 ∧ (j+31)%128=(3*m)%128) ∧
    ¬(4≤m ∧ j%64=57 ∧ (j+31)%128=(3*m)%128) ∧
    ¬(m%32=6 ∧ (j+51)%256=(9*m)%256) := by
  have hj8 : j%8=4 := by omega
  have hj32 : j%32=20 := by omega
  have hj64 : j%64=52 := by omega
  have hm32 : m%32=3 := by omega
  constructor
  · rintro ⟨_,h,_⟩
    omega
  constructor
  · rintro ⟨_,h,_⟩
    omega
  constructor
  · rintro ⟨_,h,_⟩
    omega
  · rintro ⟨h,_⟩
    omega

private theorem sub_eq_of_add_eq (x y : Nat) (h : x+2=y) :
    x=y-2 := by
  omega

private theorem affine_norm_not_four (u : Nat) (hu : 7≤u) :
    2*u-2≠4 := by
  omega

/-- The recursive affine normalizer strips every forced halving link.
    If the right counter starts at 2^(d+1)u-2, with u odd, it stops
    exactly at 2u-2. This gives a closed form for its residual right. -/
private theorem affineNormalize_pow_two (a u d : Nat)
    (ha : a%4=3) (hu : u%2=1) (huge : 3≤u) :
    (BB6.Agent15.affineNormalize a (2^(d+1)*u-2)).2=2*u-2 := by
  induction d generalizing a with
  | zero =>
      have hpow : (2:Nat)^1=2 := by decide
      have hmod : (2*u-2)%4=0 := by omega
      have hguard :
          ¬(4≤2*u-2 ∧ (2*u-2)%2=0 ∧ (a+(2*u-2))%4=1) := by
        omega
      simp [BB6.Agent15.affineNormalize,hpow,hguard]
  | succ d ih =>
      let k := 2^(d+2)*u-2
      have hp : 1≤2^d := by
        have hp0 : 0<2^d := Nat.pow_pos (by decide)
        omega
      have hsq : (2:Nat)^2=4 := by decide
      have hpow4 : 4≤2^(d+2) := by
        have hpow : 2^(d+2)=2^d*4 := by
          rw [Nat.pow_add,hsq]
        rw [hpow]
        omega
      have hmulbig : 4*3≤2^(d+2)*u :=
        Nat.mul_le_mul hpow4 huge
      have hkadd : k+2=2^(d+2)*u := by
        dsimp [k]
        exact Nat.sub_add_cancel (by omega)
      have hkbig : 4≤k := by
        rw [←hkadd] at hmulbig
        omega
      have hdiv4 : 4∣2^(d+2) := by
        have hpow : (2:Nat)^2=4 := by decide
        have h := Nat.pow_dvd_pow 2 (by omega : 2≤d+2)
        simpa only [hpow] using h
      have hdivk : 4∣k+2 := by
        rcases hdiv4 with ⟨v,hv⟩
        refine ⟨v*u,?_⟩
        rw [hkadd,hv]
        ac_rfl
      have hkmod4 : k%4=2 := by omega
      have hguard : 4≤k ∧ k%2=0 ∧ (a+k)%4=1 := by
        exact ⟨hkbig,by omega,by omega⟩
      have hpow : 2^(d+2)=2*2^(d+1) := by
        rw [Nat.pow_succ]
        ac_rfl
      have hmul : k-2=2*(2^(d+1)*u-2) := by
        dsimp [k]
        rw [hpow,Nat.mul_assoc]
        omega
      have hnext : (k-2)/2=2^(d+1)*u-2 := by omega
      have hnexta : (a+k-2)%4=3 := by omega
      rw [BB6.Agent15.affineNormalize,dif_pos hguard,hnext]
      exact ih (a+k-2) hnexta

/-- Exact arithmetic behind the new family. Its stopping target has
    inverse depth r=2m+3, strictly beyond the old r+4≤2m+2 gate. -/
private theorem late256_parameters (m : Nat)
    (hm : 259≤m) (hmres : m%256=3) :
    ∃ u : Nat,
      late256K (late256J m) m + late256J m + 3*m+5 =
        2^(2*m+2)*(late256J m+3) ∧
      late256K (late256J m) m+2=2^(2*m+3)*u ∧
      u%2=1 ∧ 7≤u ∧
      (2*late256J m+3)%4=3 ∧
      (late256K (late256J m) m+2)%2^(2*m+5)=3*2^(2*m+3) ∧
      7*2^(2*m+3)≤late256K (late256J m) m+2 := by
  let P := 2^(2*m+2)
  let j := late256J m
  let k := late256K j m
  have hPbound : 4*m+4≤P := by
    dsimp [P]
    exact BB6.Agent29New.power_linear_bound m
  have hPpos : 1≤P := by
    have hp : 0<P := by
      dsimp [P]
      exact Nat.pow_pos (by decide)
    omega
  have hJbound : 3*m+3≤9*P := by omega
  have hJplus : j+3*m+3=9*P := by
    dsimp [j]
    exact Nat.sub_add_cancel hJbound
  have hJcost : j+3*m+5=9*P+2 := by omega
  have hJ3 : j+3=9*P-3*m := by
    have hbound : 3*m≤9*P := by omega
    have hcancel := Nat.sub_add_cancel hbound
    omega
  have hqbound : 3*m+9≤9*P := by omega
  let q := 9*P-(3*m+9)
  have hqplus : q+3*m+9=9*P := by
    dsimp [q]
    exact Nat.sub_add_cancel hqbound
  have hqplus9 : q+9=9*P-3*m := by
    have hbound : 3*m≤9*P := by omega
    have hcancel := Nat.sub_add_cancel hbound
    omega
  have hPdiv8 : 8∣P := by
    have h := Nat.pow_dvd_pow 2 (by omega : 3≤2*m+2)
    simpa only [show (2:Nat)^3=8 by decide,P] using h
  have h9Pmod8 : (9*P)%8=0 := by
    have hd : 8∣9*P := by
      rcases hPdiv8 with ⟨v,hv⟩
      refine ⟨9*v,?_⟩
      rw [hv]
      ac_rfl
    exact Nat.mod_eq_zero_of_dvd hd
  have hlin8 : (3*m+9)%8=2 := by omega
  have hqsum : (q+3*m+9)%8=0 := by
    rw [hqplus]
    exact h9Pmod8
  have hqmod8 : q%8=6 := by
    rw [Nat.add_mod] at hqsum
    omega
  have hqbound14 : 14≤q := by
    dsimp [q,P]
    omega
  let u := q/2
  have hqu : q=2*u := by
    dsimp [u]
    omega
  have huodd : u%2=1 := by
    rw [hqu] at hqmod8
    omega
  have huge : 7≤u := by
    rw [hqu] at hqbound14
    omega
  have hscore : j+3*m+5≤P*(j+3) := by
    have hjle : j≤P*j := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hPpos
    have hmargin : 3*m+5≤3*P := by omega
    rw [Nat.mul_add]
    rw [Nat.mul_comm P 3]
    omega
  have hkstop' : k+(j+3*m+5)=P*(j+3) := by
    dsimp [k,late256K]
    simpa [P] using Nat.sub_add_cancel hscore
  have hkstop : k+j+3*m+5=P*(j+3) := by
    omega
  have hstop' : k+(9*P+2)=P*(q+9) := by
    calc
      k+(9*P+2)=k+(j+3*m+5) := by rw [hJcost]
      _=P*(j+3) := by omega
      _=P*(q+9) := by rw [hJ3,hqplus9]
  have hmul : P*(q+9)=P*q+9*P := by
    rw [Nat.mul_add]
    rw [Nat.mul_comm P 9]
  have hkplus : k+2=P*q := by
    rw [hmul] at hstop'
    omega
  have hpowr : (2:Nat)^(2*m+3)=2*P := by
    dsimp [P]
    rw [show 2*m+3=(2*m+2)+1 by omega,Nat.pow_succ]
    omega
  have hkpow : k+2=2^(2*m+3)*u := by
    calc
      k+2=P*q := hkplus
      _=P*(2*u) := by rw [hqu]
      _=(2*P)*u := by
        simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
      _=2^(2*m+3)*u := by rw [hpowr]
  have hqrepr : q=8*(q/8)+6 := by
    have h := Nat.mod_add_div q 8
    rw [hqmod8] at h
    omega
  have hkrepr : k+2=8*P*(q/8)+6*P := by
    calc
      k+2=P*q := hkplus
      _=P*(8*(q/8)+6) := by
        exact congrArg (fun x : Nat => P*x) hqrepr
      _=8*P*(q/8)+6*P := by
        rw [Nat.mul_add]
        simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  have hmodulus : (2:Nat)^(2*m+5)=8*P := by
    dsimp [P]
    rw [show 2*m+5=(2*m+2)+3 by omega,Nat.pow_add]
    simp only [show (2:Nat)^3=8 by decide]
    omega
  have hdiv : 8*P∣8*P*(q/8) := by
    refine ⟨q/8,?_⟩
    ac_rfl
  have hlt : 6*P<8*P := by omega
  have hmod : (k+2)%(2:Nat)^(2*m+5)=3*2^(2*m+3) := by
    rw [hmodulus,hkrepr]
    calc
      (8*P*(q/8)+6*P)%(8*P)
        =((8*P*(q/8))%(8*P)+(6*P)%(8*P))%(8*P) := by rw [Nat.add_mod]
      _=6*P := by
        have hzero : (8*P*(q/8))%(8*P)=0 :=
          Nat.mod_eq_zero_of_dvd hdiv
        have hrem : (6*P)%(8*P)=6*P := Nat.mod_eq_of_lt hlt
        rw [Nat.add_mod,hzero]
        simpa using hrem
      _=3*(2*P) := by omega
      _=3*2^(2*m+3) := by rw [hpowr]
  have hsize : 7*2^(2*m+3)≤k+2 := by
    rw [hkpow]
    simpa [Nat.mul_comm] using
      Nat.mul_le_mul_left (2^(2*m+3)) huge
  have hjmod256 := late256_j_mod256 m hm hmres
  have hjmod256' : j%256=244 := by simpa [j] using hjmod256
  have hleft : (2*j+3)%4=3 :=
    left_mod4_of_jmod256 j hjmod256'
  refine ⟨u,hkstop,hkpow,huodd,huge,hleft,hmod,hsize⟩

/-- The complementary odd-part-three cone now excludes every member of
    the infinite family m=3 mod 256, j=9*2^(2m+2)-3m-3. -/
theorem late256_no_blank (m : Nat)
    (hm : 259≤m) (hmres : m%256=3) :
    ¬BB6.Agent3.CReach (2*late256J m+3)
      (late256K (late256J m) m) := by
  obtain ⟨u,hstop,hkpow,huodd,huge,hleft,hmod,hsize⟩ :=
    late256_parameters m hm hmres
  have hr : 2≤2*m+3 := by omega
  have hm4 : m%4=(2*(2*m+3)+1)%4 := by omega
  exact BB6.Agent11HighThreeLate.late_high_no_blank
    (2*m+3) (late256J m) m (late256K (late256J m) m)
    hr (by omega) hm4 hstop hmod hsize

/-- The new family is admitted by the previous Agent19/29/3/11
    ValSixFull+C58 sieve, by the all-depth dyadic gate, by the Boolean
    implementation of that gate, and by the earlier depth-seven family. -/
theorem old_sieve_admits_late256_family (m : Nat)
    (hm : 259≤m) (hmres : m%256=3) :
    BB6.Agent11C58Late.highAllowed (late256J m) m := by
  let j := late256J m
  let P := 2^(2*m+2)
  obtain ⟨u,hstop,hkpow,huodd,huge,hleft,hmod,hsize⟩ :=
    late256_parameters m hm hmres
  have hsum := late256_sum_identity m hm
  have hjmod256 := late256_j_mod256 m hm hmres
  have hJoint : BB6.Agent19Joint.highAllowed j m := by
    unfold BB6.Agent19Joint.highAllowed
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · simp [BB6.Agent3.jointHighRectAllowed,
        BB6.Agent3.jointHighAllowed] <;> omega
    · intro n
      rintro ⟨hdepth,hpair,_⟩
      have hdiv : 2^(n+4)∣P := Nat.pow_dvd_pow 2 hdepth
      have hdiv9 : 2^(n+4)∣9*P := by
        rcases hdiv with ⟨v,hv⟩
        refine ⟨9*v,?_⟩
        rw [hv]
        ac_rfl
      have hzero : (j+3*m+3)%2^(n+4)=0 := by
        rw [show j+3*m+3=9*P by simpa [P] using hsum]
        exact Nat.mod_eq_zero_of_dvd hdiv9
      rw [hzero] at hpair
      have hpos : 0<2^(n+2) := Nat.pow_pos (by decide)
      omega
    · omega
    · omega
    · omega
    · omega
  have hjmod256' : j%256=244 := by simpa [j] using hjmod256
  have hExtra := highAllowedPlus_extras_of_mod256 j m hjmod256' hmres
  have hPlus : BB6.Agent29Joint.highAllowedPlus j m := by
    unfold BB6.Agent29Joint.highAllowedPlus
    exact ⟨hJoint,hExtra.1,hExtra.2.1,hExtra.2.2.1,hExtra.2.2.2⟩
  have hValSix : BB6.Agent3ValSix.highAllowedValSix j m := by
    unfold BB6.Agent3ValSix.highAllowedValSix
    exact ⟨hPlus,by omega,by omega⟩
  have hThree : BB6.Agent3ValSix.highAllowedValSixThree j m := by
    unfold BB6.Agent3ValSix.highAllowedValSixThree
    exact ⟨hValSix,by omega⟩
  have h11 : BB6.Agent11Joint.highAllowed j m := by
    unfold BB6.Agent11Joint.highAllowed
    exact ⟨hJoint,by omega,by omega⟩
  have hFive : BB6.Agent19Five.highAllowed j m := by
    unfold BB6.Agent19Five.highAllowed
    exact ⟨h11,by omega⟩
  have hnorm : (BB6.Agent15.affineNormalize (2*j+3)
      (late256K j m)).2=2*u-2 := by
    have hkpow' : late256K j m+2=2^(2*m+3)*u := by
      simpa [j] using hkpow
    have hkEq : late256K j m=2^(2*m+3)*u-2 :=
      sub_eq_of_add_eq _ _ hkpow'
    rw [hkEq]
    exact affineNormalize_pow_two (2*j+3) u (2*m+2)
      hleft huodd (by omega)
  have hAffine : (BB6.Agent15.affineNormalize (2*j+3)
      (late256K j m)).2≠4 := by
    rw [hnorm]
    exact affine_norm_not_four u huge
  have hFull : BB6.Agent3ValSix.highAllowedValSixFull j m := by
    unfold BB6.Agent3ValSix.highAllowedValSixFull
    exact ⟨hThree,hFive,by omega,by omega,by omega,hAffine⟩
  have hC58 : BB6.Agent11C58ValSix.highAllowed j m := by
    unfold BB6.Agent11C58ValSix.highAllowed
    exact ⟨hFull,by omega⟩
  have hsumOdd : (j+9*m+14)%2=1 := by
    have hform : j+9*m+14=9*P+6*m+11 := by
      have hP := BB6.Agent29New.power_linear_bound m
      dsimp [j,late256J,P]
      omega
    have hdiv2 : 2∣P := by
      have h := Nat.pow_dvd_pow 2 (by omega : 1≤2*m+2)
      simpa only [show (2:Nat)^1=2 by decide,P] using h
    rw [hform]
    have hPmod : P%2=0 := Nat.mod_eq_zero_of_dvd hdiv2
    omega
  have hNoGate : ∀ r : Nat, ¬BB6.Agent11GateDecision.gate r j m := by
    intro r hgate
    have hdiv4 : 4∣(2:Nat)^(r+4) := by
      have h := Nat.pow_dvd_pow 2 (by omega : 2≤r+4)
      simpa only [show (2:Nat)^2=4 by decide] using h
    have hmod4 : (j+9*m+14)%4=
        ((j+9*m+14)%(2:Nat)^(r+4))%4 :=
      (Nat.mod_mod_of_dvd _ hdiv4).symm
    rw [hgate.2.2.2.2] at hmod4
    have hdivrhs : 4∣3*(2:Nat)^(r+2) := by
      have h := Nat.pow_dvd_pow 2 (by omega : 2≤r+2)
      rcases h with ⟨v,hv⟩
      refine ⟨3*v,?_⟩
      rw [hv]
      ac_rfl
    have hrhs : (3*(2:Nat)^(r+2))%4=0 :=
      Nat.mod_eq_zero_of_dvd hdivrhs
    rw [hrhs] at hmod4
    have hleft2 : ((j+9*m+14)%4)%2=1 := by
      rw [Nat.mod_mod_of_dvd _ (by decide : 2∣4)]
      exact hsumOdd
    rw [hmod4] at hleft2
    omega
  have hAll : BB6.Agent11C58AllDepth.highAllowed j m :=
    ⟨hC58,hNoGate⟩
  have hBool : BB6.Agent11C58Boolean.highAllowed j m :=
    (BB6.Agent11C58Boolean.highAllowed_iff j m).mpr hAll
  unfold BB6.Agent11C58Late.highAllowed
  exact ⟨hBool,by omega⟩

/-- A complete lossless Machine C blank-halting iff after adding the
    new all-time high family. The remaining low/high parameter
    existentials are still unbounded. -/
theorem blank_halts_iff_c58_all_depth_late_256 :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11C58ValSix.lowAllowed m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision 1
          (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowed j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent11C58Late.blank_halts_iff_c58_all_depth_late]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · have hnot : ¬(259≤m ∧ m%256=3 ∧ j=late256J m) := by
        rintro ⟨hm,hmres,hj⟩
        subst j
        have hreach : BB6.Agent3.CReach
            (2*late256J m+3)
            (2^(2*m+2)*(late256J m+3)-(late256J m+3*m+5)) :=
          (BB6.Agent3ValSix.valSixMixedRootDecision_iff _ _).mp hroot
        have hreach' : BB6.Agent3.CReach
            (2*late256J m+3) (late256K (late256J m) m) := by
          simpa [late256K] using hreach
        exact (late256_no_blank m hm hmres) hreach'
      exact Or.inr ⟨j,m,⟨hprior,hnot⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

/-- The explicit sequence m=256t+3 supplies infinitely many parameters
    admitted by the entire previous C58/ValSix sieve and removed here. -/
theorem late256_new_strict_family (t : Nat) (ht : 1≤t) :
    BB6.Agent11C58Late.highAllowed
      (late256J (256*t+3)) (256*t+3) ∧
    ¬highAllowed (late256J (256*t+3)) (256*t+3) := by
  have hm : 259≤256*t+3 := by omega
  have hmres : (256*t+3)%256=3 := by omega
  refine ⟨old_sieve_admits_late256_family (256*t+3) hm hmres,?_⟩
  intro h
  exact h.2 ⟨hm,hmres,rfl⟩

#print axioms late256_no_blank
#print axioms old_sieve_admits_late256_family
#print axioms blank_halts_iff_c58_all_depth_late_256
#print axioms late256_new_strict_family

end BB6.Agent19HighThreeLate256
