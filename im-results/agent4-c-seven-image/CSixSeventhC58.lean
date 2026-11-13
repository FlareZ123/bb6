import ValSixC58LateFast
import CSixSeventhDiagonal
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4SevenC58

/-- The four-class diagonal forces these exact low residues. -/
private theorem diagonal_residues (j m : Nat)
    (hj : j%512=319)
    (hpair : (3*m)%4096=(j+2879)%4096) :
    j%256=63 ∧ j%128=63 ∧ j%64=63 ∧ j%32=31 ∧
    j%16=15 ∧ j%8=7 ∧ j%4=3 ∧
    m%512=42 ∧ m%256=42 ∧ m%128=42 ∧ m%64=42 ∧
    m%32=10 ∧ m%16=10 ∧ m%8=2 ∧ m%4=2 := by
  have hdiv : 512 ∣ 4096 := by decide
  have h3m : (3*m)%512=126 := by
    calc
      (3*m)%512 = ((3*m)%4096)%512 := by
        symm
        exact Nat.mod_mod_of_dvd (3*m) hdiv
      _ = ((j+2879)%4096)%512 := by rw [hpair]
      _ = (j+2879)%512 := Nat.mod_mod_of_dvd (j+2879) hdiv
      _ = 126 := by omega
  have hm512 : m%512=42 := by omega
  omega

private theorem high_score_nonnegative (j m : Nat) :
    j+3*m+5 ≤ (2:Nat)^(2*m+2)*(j+3) := by
  have hP : 4*m+4 ≤ (2:Nat)^(2*m+2) :=
    BB6.Agent29New.power_linear_bound m
  have hp : 1 ≤ (2:Nat)^(2*m+2) :=
    Nat.pow_pos (by decide)
  have hj : j ≤ (2:Nat)^(2*m+2)*j := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right j hp
  have hm : 3*m+5 ≤ 3*(2:Nat)^(2*m+2) := by omega
  rw [Nat.mul_add]
  omega

private theorem high_stop_identity (j m : Nat) :
    (2:Nat)^(2*m+2)*(j+3) - (j+3*m+5) + j+3*m+5 =
      (2:Nat)^(2*m+2)*(j+3) := by
  have h := Nat.sub_add_cancel (high_score_nonnegative j m)
  omega

private theorem residue_vector_of_mod512 (j m : Nat)
    (hj : j%512=319) (hm512 : m%512=42) :
    j%256=63 ∧ j%128=63 ∧ j%64=63 ∧ j%32=31 ∧
    j%16=15 ∧ j%8=7 ∧ j%4=3 ∧
    m%256=42 ∧ m%128=42 ∧ m%64=42 ∧
    m%32=10 ∧ m%16=10 ∧ m%8=2 ∧ m%4=2 := by
  omega

/-- The residue pair j=319 (mod 512), m=42 (mod 512)
    is admitted by the complete source-certified ValSixFull+C58
    all-depth high sieve, including its affine right-four exclusion. -/
private theorem prior_c58_admits_residue_pair (j m : Nat)
    (hm : 7≤m) (hj : j%512=319) (hm512 : m%512=42) :
    BB6.Agent11C58AllDepth.highAllowed j m := by
  obtain ⟨hj256,hj128,hj64,hj32,hj16,hj8,hj4,
      hm256,hm128,hm64,hm32,hm16,hm8,hm4⟩ :=
    residue_vector_of_mod512 j m hj hm512

  have hbase : BB6.Agent3.jointHighAllowed j m := by
    unfold BB6.Agent3.jointHighAllowed
    refine ⟨?_,?_,?_,?_,?_⟩ <;> omega
  have hrect : BB6.Agent3.jointHighRectAllowed j m := by
    unfold BB6.Agent3.jointHighRectAllowed
    exact ⟨hbase,by omega⟩

  have hdyadic : ∀ n, ¬(n+4≤2*m+2 ∧
      (j+3*m+3)%2^(n+4)=2^(n+2) ∧
      (2*j+3)%8=(if n%2=0 then 7 else 3)) := by
    intro n
    rintro ⟨_,hpar,hx⟩
    have hx1 : (2*j+3)%8=1 := by omega
    by_cases hn : n%2=0
    · simp [hn] at hx
      omega
    · simp [hn] at hx
      omega

  have h19 : BB6.Agent19Joint.highAllowed j m := by
    unfold BB6.Agent19Joint.highAllowed
    exact ⟨hrect,hdyadic,by omega,by omega,by omega,by omega⟩
  have hplus : BB6.Agent29Joint.highAllowedPlus j m := by
    unfold BB6.Agent29Joint.highAllowedPlus
    exact ⟨h19,by omega,by omega,by omega,by omega⟩
  have hvalThree : BB6.Agent3ValSix.highAllowedValSixThree j m := by
    unfold BB6.Agent3ValSix.highAllowedValSixThree
    unfold BB6.Agent3ValSix.highAllowedValSix
    exact ⟨⟨hplus,by omega,by omega⟩,by omega⟩
  have h11 : BB6.Agent11Joint.highAllowed j m := by
    unfold BB6.Agent11Joint.highAllowed
    exact ⟨h19,by omega,by omega⟩
  have hfive : BB6.Agent19Five.highAllowed j m := by
    unfold BB6.Agent19Five.highAllowed
    exact ⟨h11,by omega⟩

  let k := (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)
  have hstop : k+j+3*m+5=(2:Nat)^(2*m+2)*(j+3) := by
    simpa [k] using high_stop_identity j m
  have hpow4 : 4 ∣ (2:Nat)^(2*m+2) := by
    have hpow : (2:Nat)^2 ∣ (2:Nat)^(2*m+2) :=
      Nat.pow_dvd_pow 2 (by omega)
    simpa only [show (2:Nat)^2=4 by decide] using hpow
  have hprod4 : 4 ∣ (2:Nat)^(2*m+2)*(j+3) := by
    rcases hpow4 with ⟨q,hq⟩
    refine ⟨q*(j+3),?_⟩
    rw [hq]
    ac_rfl
  have hmod0 : (k+j+3*m+5)%4=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hprod4
  have hk4 : k%4=2 := by omega
  have hguard : ¬(4≤k ∧ k%2=0 ∧ ((2*j+3)+k)%4=1) := by omega
  have hnorm :
      BB6.Agent15.affineNormalize (2*j+3) k=(2*j+3,k) := by
    simp [BB6.Agent15.affineNormalize,hguard]
  have hright4 :
      (BB6.Agent15.affineNormalize (2*j+3) k).2≠4 := by
    rw [hnorm]
    omega

  have hfull : BB6.Agent3ValSix.highAllowedValSixFull j m := by
    unfold BB6.Agent3ValSix.highAllowedValSixFull
    exact ⟨hvalThree,hfive,by omega,by omega,by omega,hright4⟩
  have hc58 : BB6.Agent11C58ValSix.highAllowed j m := by
    unfold BB6.Agent11C58ValSix.highAllowed
    exact ⟨hfull,by omega⟩
  unfold BB6.Agent11C58AllDepth.highAllowed
  refine ⟨hc58,?_⟩
  intro r
  rintro ⟨_,_,_,hmr,hres⟩
  have hodd : (2*r+3)%4=1 ∨ (2*r+3)%4=3 := by omega
  omega


/-- The original six/seven diagonal is a special case of the residue-pair
    admission lemma. -/
theorem prior_c58_admits_six_seven_diagonal (j m : Nat)
    (hm : 7≤m) (hj : j%512=319)
    (hpair : (3*m)%4096=(j+2879)%4096) :
    BB6.Agent11C58AllDepth.highAllowed j m := by
  obtain ⟨_,_,_,_,_,_,_,hm512,_,_,_,_,_,_,_⟩ :=
    diagonal_residues j m hj hpair
  exact prior_c58_admits_residue_pair j m hm hj hm512

/-- A concrete infinite progression survives every preceding
    ValSixFull+C58 all-depth restriction. -/
theorem prior_c58_admits_concrete_infinite_family (t : Nat) :
    BB6.Agent11C58AllDepth.highAllowed (1343+4096*t) 42 := by
  apply prior_c58_admits_six_seven_diagonal
  · omega
  · omega
  · omega

/-- The same diagonal is admitted even by the newer arbitrary-depth
    late three-cone filter, not merely by the earlier all-depth gate. -/
theorem prior_latefast_admits_six_seven_diagonal (j m : Nat)
    (hm : 7≤m) (hj : j%512=319)
    (hpair : (3*m)%4096=(j+2879)%4096) :
    BB6.Agent11LateFastWrapper.highAllowed j m := by
  have hprior := prior_c58_admits_six_seven_diagonal j m hm hj hpair
  have hbool : BB6.Agent11C58Boolean.highAllowed j m :=
    (BB6.Agent11C58Boolean.highAllowed_iff j m).mpr hprior
  have hlate : BB6.Agent11LateDepthGate.allowedBool j m = true := by
    apply (BB6.Agent11LateDepthGate.allowedBool_iff j m).mpr
    intro r hr
    rcases hr with ⟨hrmin,hm3,hm4,hmod,hsize⟩
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hm4diag⟩ :=
      diagonal_residues j m hj hpair
    have hodd : (2*r+1)%4=1 ∨ (2*r+1)%4=3 := by omega
    omega
  exact ⟨hbool,hlate⟩

/-- The concrete progression also survives the arbitrary-depth late
    filter, so the new diagonal exclusion is independent of that gate. -/
theorem prior_latefast_admits_concrete_infinite_family (t : Nat) :
    BB6.Agent11LateFastWrapper.highAllowed (1343+4096*t) 42 := by
  apply prior_latefast_admits_six_seven_diagonal
  · omega
  · omega
  · omega

/-- Strengthen the latest late-fast high predicate by the independent
    six/seven source-certified diagonal. -/
def lateFastHighAllowed (j m : Nat) : Prop :=
  BB6.Agent11LateFastWrapper.highAllowed j m ∧
  ¬(7≤m ∧ j%512=319 ∧
    (3*m)%4096=(j+2879)%4096)

/-- A second explicit high-stop parameter progression survives all
    current C58/late-fast filters: j=831, m=9770 (mod 16384). -/
theorem prior_latefast_admits_s3_parameter_family (t : Nat) :
    lateFastHighAllowed 831 (9770+16384*t) := by
  let m := 9770+16384*t
  have hm7 : 7≤m := by dsimp [m]; omega
  have hj : 831%512=319 := by decide
  have hm512 : m%512=42 := by dsimp [m]; omega
  have hprior := prior_c58_admits_residue_pair 831 m hm7 hj hm512
  have hbool : BB6.Agent11C58Boolean.highAllowed 831 m :=
    (BB6.Agent11C58Boolean.highAllowed_iff 831 m).mpr hprior
  have hlate : BB6.Agent11LateDepthGate.allowedBool 831 m=true := by
    apply (BB6.Agent11LateDepthGate.allowedBool_iff 831 m).mpr
    intro r hr
    rcases hr with ⟨hrmin,hm3,hm4,hmod,hsize⟩
    have hm4res : m%4=2 := by dsimp [m]; omega
    have hodd : (2*r+1)%4=1 ∨ (2*r+1)%4=3 := by omega
    omega
  have hnotdiag :
      ¬(7≤m ∧ 831%512=319 ∧
        (3*m)%4096=(831+2879)%4096) := by
    rintro ⟨_,_,hpair⟩
    have h3m : (3*m)%4096=638 := by dsimp [m]; omega
    have hjmod : (831+2879)%4096=3710 := by decide
    omega
  exact ⟨⟨hbool,hlate⟩,hnotdiag⟩

/-- A second explicit high-stop progression, in the other residue
    slice u=3 (mod 4), u+v=11 (mod 16), also survives all current
    C58/late-fast filters. -/
theorem prior_latefast_admits_s3_second_parameter_family (t : Nat) :
    lateFastHighAllowed 1855 (12842+16384*t) := by
  let m := 12842+16384*t
  have hm7 : 7≤m := by dsimp [m]; omega
  have hj : 1855%512=319 := by decide
  have hm512 : m%512=42 := by dsimp [m]; omega
  have hprior := prior_c58_admits_residue_pair 1855 m hm7 hj hm512
  have hbool : BB6.Agent11C58Boolean.highAllowed 1855 m :=
    (BB6.Agent11C58Boolean.highAllowed_iff 1855 m).mpr hprior
  have hlate : BB6.Agent11LateDepthGate.allowedBool 1855 m=true := by
    apply (BB6.Agent11LateDepthGate.allowedBool_iff 1855 m).mpr
    intro r hr
    rcases hr with ⟨hrmin,hm3,hm4,hmod,hsize⟩
    have hm4res : m%4=2 := by dsimp [m]; omega
    have hodd : (2*r+1)%4=1 ∨ (2*r+1)%4=3 := by omega
    omega
  have hnotdiag :
      ¬(7≤m ∧ 1855%512=319 ∧
        (3*m)%4096=(1855+2879)%4096) := by
    rintro ⟨_,_,hpair⟩
    have h3m : (3*m)%4096=1662 := by dsimp [m]; omega
    have hjmod : (1855+2879)%4096=638 := by decide
    omega
  exact ⟨⟨hbool,hlate⟩,hnotdiag⟩

/-- Every high-stop parameter whose exact stopping target lies in
    the second strict image family is admitted by the preceding
    ValSixFull+C58 all-depth and arbitrary-depth late-fast predicates.
    Its disjointness from the old diagonal follows from u+v=3 (mod 4). -/
theorem prior_latefast_admits_s3_image_family (j m u v : Nat)
    (hm7 : 7≤m)
    (hj : j=319+512*u)
    (hk : (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)=574+1024*v)
    (hsector : (u+v)%16=(15+4*u)%16) :
    lateFastHighAllowed j m := by
  let k := (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)
  have hstop : k+j+3*m+5=(2:Nat)^(2*m+2)*(j+3) := by
    simpa [k] using high_stop_identity j m
  have hj512 : j%512=319 := by rw [hj]; omega
  have hpow512 : 512 ∣ (2:Nat)^(2*m+2) := by
    have h := Nat.pow_dvd_pow 2 (by omega : 9≤2*m+2)
    simpa only [show (2:Nat)^9=512 by decide] using h
  have hprod512 : 512 ∣ (2:Nat)^(2*m+2)*(j+3) := by
    rcases hpow512 with ⟨q,hq⟩
    refine ⟨q*(j+3),?_⟩
    rw [hq]
    ac_rfl
  have hstopmod512 : (k+j+3*m+5)%512=0 := by
    rw [hstop]
    exact Nat.mod_eq_zero_of_dvd hprod512
  have hm512 : m%512=42 := by
    rw [hk,hj] at hstopmod512
    omega
  have hprior := prior_c58_admits_residue_pair j m hm7 hj512 hm512
  have hbool : BB6.Agent11C58Boolean.highAllowed j m :=
    (BB6.Agent11C58Boolean.highAllowed_iff j m).mpr hprior
  have hlate : BB6.Agent11LateDepthGate.allowedBool j m=true := by
    apply (BB6.Agent11LateDepthGate.allowedBool_iff j m).mpr
    intro r hr
    rcases hr with ⟨hrmin,hm3,hm4,hmod,hsize⟩
    have hm4res : m%4=2 := by omega
    have hodd : (2*r+1)%4=1 ∨ (2*r+1)%4=3 := by omega
    omega
  have hnotdiag :
      ¬(7≤m ∧ j%512=319 ∧
        (3*m)%4096=(j+2879)%4096) := by
    rintro ⟨_,_,hpair⟩
    have hpow4096 : 4096 ∣ (2:Nat)^(2*m+2) := by
      have h := Nat.pow_dvd_pow 2 (by omega : 12≤2*m+2)
      simpa only [show (2:Nat)^12=4096 by decide] using h
    have hprod4096 : 4096 ∣ (2:Nat)^(2*m+2)*(j+3) := by
      rcases hpow4096 with ⟨q,hq⟩
      refine ⟨q*(j+3),?_⟩
      rw [hq]
      ac_rfl
    have hstopmod4096 : (k+j+3*m+5)%4096=0 := by
      rw [hstop]
      exact Nat.mod_eq_zero_of_dvd hprod4096
    have hsector4 : (u+v)%4=3 := by omega
    rw [hk,hj] at hstopmod4096
    omega
  exact ⟨⟨hbool,hlate⟩,hnotdiag⟩

/-- Exact original-source Machine C blank-halting iff after adding
    Agent 4's diagonal to the C58 all-depth plus arbitrary-depth
    late three-cone high predicate. -/
theorem blank_halts_iff_c58_late_fast_six_seven :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11C58ValSix.lowAllowed m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision
          1 (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, lateFastHighAllowed j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent11LateFastWrapper.blank_halts_iff_c58_all_depth_late_fast]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · let k := (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)
      have hreach : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff (2*j+3) k).mp hroot
      have hnot : ¬(7≤m ∧ j%512=319 ∧
          (3*m)%4096=(j+2879)%4096) := by
        rintro ⟨hm,hj,hpair⟩
        obtain ⟨time,hrun⟩ := hreach
        have hstop : k+j+3*m+5=(2:Nat)^(2*m+2)*(j+3) := by
          simpa [k] using high_stop_identity j m
        exact (BB6.Agent4Seven.high_stop_six_seven_diagonal
          j m k time hm hj hpair hstop) hrun
      exact Or.inr ⟨j,m,⟨hprior,by simpa [k] using hnot⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨⟨hprior,hlate⟩,hnotdiag⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,⟨hprior,hlate⟩,hroot⟩

/-- The concrete infinite progression is excluded by the latest
    late-fast exact high predicate, despite passing all earlier gates. -/
theorem latefast_concrete_family_removed (t : Nat) :
    ¬lateFastHighAllowed (1343+4096*t) 42 := by
  intro h
  exact h.2 ⟨by omega,by omega,by omega⟩

/-- The stronger exact high predicate removes the whole six/seven
    source-certified diagonal, without changing the low branch. -/
def highAllowed (j m : Nat) : Prop :=
  BB6.Agent11C58AllDepth.highAllowed j m ∧
  ¬(7≤m ∧ j%512=319 ∧
    (3*m)%4096=(j+2879)%4096)

/-- Exact original-source Machine C blank-halting iff after adding
    Agent 4's independent infinite six/seven high-stop exclusion.
    The remaining parameter existentials are still unbounded. -/
theorem blank_halts_iff_c58_all_depth_six_seven :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11C58ValSix.lowAllowed m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision
          1 (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowed j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [BB6.Agent11C58AllDepth.blank_halts_iff_joint_c58_all_depth]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · let k := (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)
      have hreach : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff (2*j+3) k).mp hroot
      have hnot : ¬(7≤m ∧ j%512=319 ∧
          (3*m)%4096=(j+2879)%4096) := by
        rintro ⟨hm,hj,hpair⟩
        obtain ⟨time,hrun⟩ := hreach
        have hstop : k+j+3*m+5=(2:Nat)^(2*m+2)*(j+3) := by
          simpa [k] using high_stop_identity j m
        exact (BB6.Agent4Seven.high_stop_six_seven_diagonal
          j m k time hm hj hpair hstop) hrun
      exact Or.inr ⟨j,m,⟨hprior,hnot⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨⟨hprior,hdepth⟩,hnotdiag⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,⟨hprior,hdepth⟩,hroot⟩

/-- The explicit infinite progression is excluded by the new exact
    high predicate, despite being admitted by the prior one. -/
theorem concrete_family_removed (t : Nat) :
    ¬highAllowed (1343+4096*t) 42 := by
  intro h
  exact h.2 ⟨by omega,by omega,by omega⟩

/-- The exact high stop with j=831 and m=9770 (mod 16384)
    lands in the second strict sixth/seventh image slice u=1,
    v=2 (mod 16). -/
private theorem s3_high_target (t : Nat) :
    ∃ v, (2:Nat)^(2*(9770+16384*t)+2)*(831+3) -
      (831+3*(9770+16384*t)+5)=574+1024*v ∧ v%16=2 := by
  let m := 9770+16384*t
  let k := (2:Nat)^(2*m+2)*(831+3)-(831+3*m+5)
  have hm7 : 7≤m := by dsimp [m]; omega
  have hpow : 16384 ∣ (2:Nat)^(2*m+2) := by
    have h := Nat.pow_dvd_pow 2 (by omega : 14≤2*m+2)
    simpa only [show (2:Nat)^14=16384 by decide] using h
  have hprod : 16384 ∣ (2:Nat)^(2*m+2)*(831+3) := by
    rcases hpow with ⟨q,hq⟩
    refine ⟨q*(831+3),?_⟩
    rw [hq]
    ac_rfl
  have hstop : k+831+3*m+5=(2:Nat)^(2*m+2)*(831+3) := by
    simpa [k] using high_stop_identity 831 m
  have hmres : m%16384=9770 := by dsimp [m]; omega
  have h3m : (3*m)%16384=12926 := by omega
  have hPmod : ((2:Nat)^(2*m+2)*(831+3))%16384=0 :=
    Nat.mod_eq_zero_of_dvd hprod
  have hkmod : k%16384=2622 := by omega
  have hdiv : 1024 ∣ 16384 := by decide
  have hkmod1024 : k%1024=574 := by
    calc
      k%1024 = (k%16384)%1024 :=
        (Nat.mod_mod_of_dvd k hdiv).symm
      _ = 2622%1024 := by rw [hkmod]
      _ = 574 := by decide
  let v := k/1024
  have hdecomp : k%1024+1024*(k/1024)=k :=
    Nat.mod_add_div k 1024
  have hkv : k=574+1024*v := by
    dsimp [v]
    omega
  have hv16 : v%16=2 := by
    rw [hkv] at hkmod
    omega
  refine ⟨v,?_,hv16⟩
  simpa [m,k] using hkv

/-- The new s3 strict-image family excludes these exact high-stop
    parameters from the original blank-root orbit. -/
private theorem s3_high_parameter_no_blank (t time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*831+3,
        (2:Nat)^(2*(9770+16384*t)+2)*(831+3) -
          (831+3*(9770+16384*t)+5)) := by
  obtain ⟨v,hkv,hv16⟩ := s3_high_target t
  have hsector : (1+v)%16=(15+4*1)%16 := by omega
  have hblank := BB6.Agent4Seven.blank_ne_six_seven_band_s3 1 v time hsector
  intro hrun
  apply hblank
  have hx : 2*831+3=641+1024*1 := by decide
  rw [hx,hkv] at hrun
  exact hrun

/-- The second exact high stop lands in the other strict image slice:
    j=1855 and m=12842 (mod 16384) give u=3 and v=8 (mod 16). -/
private theorem s3_high_target_second (t : Nat) :
    ∃ v, (2:Nat)^(2*(12842+16384*t)+2)*(1855+3) -
      (1855+3*(12842+16384*t)+5)=574+1024*v ∧ v%16=8 := by
  let m := 12842+16384*t
  let k := (2:Nat)^(2*m+2)*(1855+3)-(1855+3*m+5)
  have hm7 : 7≤m := by dsimp [m]; omega
  have hpow : 16384 ∣ (2:Nat)^(2*m+2) := by
    have h := Nat.pow_dvd_pow 2 (by omega : 14≤2*m+2)
    simpa only [show (2:Nat)^14=16384 by decide] using h
  have hprod : 16384 ∣ (2:Nat)^(2*m+2)*(1855+3) := by
    rcases hpow with ⟨q,hq⟩
    refine ⟨q*(1855+3),?_⟩
    rw [hq]
    ac_rfl
  have hstop : k+1855+3*m+5=(2:Nat)^(2*m+2)*(1855+3) := by
    simpa [k] using high_stop_identity 1855 m
  have hmres : m%16384=12842 := by dsimp [m]; omega
  have h3m : (3*m)%16384=5758 := by omega
  have hPmod : ((2:Nat)^(2*m+2)*(1855+3))%16384=0 :=
    Nat.mod_eq_zero_of_dvd hprod
  have hkmod : k%16384=8766 := by omega
  have hdiv : 1024 ∣ 16384 := by decide
  have hkmod1024 : k%1024=574 := by
    calc
      k%1024 = (k%16384)%1024 :=
        (Nat.mod_mod_of_dvd k hdiv).symm
      _ = 8766%1024 := by rw [hkmod]
      _ = 574 := by decide
  let v := k/1024
  have hdecomp : k%1024+1024*(k/1024)=k :=
    Nat.mod_add_div k 1024
  have hkv : k=574+1024*v := by
    dsimp [v]
    omega
  have hv16 : v%16=8 := by
    rw [hkv] at hkmod
    omega
  refine ⟨v,?_,hv16⟩
  simpa [m,k] using hkv

/-- The second exact high-stop progression is excluded by the
    second strict image slice at every time. -/
private theorem s3_high_parameter_no_blank_second (t time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*1855+3,
        (2:Nat)^(2*(12842+16384*t)+2)*(1855+3) -
          (1855+3*(12842+16384*t)+5)) := by
  obtain ⟨v,hkv,hv16⟩ := s3_high_target_second t
  have hsector : (3+v)%16=(15+4*3)%16 := by omega
  have hblank := BB6.Agent4Seven.blank_ne_six_seven_band_s3 3 v time hsector
  intro hrun
  apply hblank
  have hx : 2*1855+3=641+1024*3 := by decide
  rw [hx,hkv] at hrun
  exact hrun

/-- The second strict s3 image family has an exact parameter-only
    pullback: one residue for j modulo 512 and one affine residue for m
    modulo 16384. -/
private theorem s3_pullback_forces_m_ge7 (j m u v : Nat)
    (hj : j=319+512*u)
    (hk : (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)=574+1024*v) :
    7≤m := by
  have hstop : (574+1024*v)+j+3*m+5 =
      (2:Nat)^(2*m+2)*(j+3) := by
    rw [← hk]
    exact Nat.sub_add_cancel (high_score_nonnegative j m)
  rw [hj] at hstop
  by_contra hm
  have hmle : m≤6 := by omega
  rcases (show m=0 ∨ m=1 ∨ m=2 ∨ m=3 ∨ m=4 ∨ m=5 ∨ m=6 by omega)
    with h0|h1|h2|h3|h4|h5|h6
  all_goals subst m
  all_goals simp at hstop
  all_goals omega

/-- Exact equivalence between the second strict image-family pullback
    and its single affine high-stop congruence cylinder. -/
theorem s3_image_pullback_iff_congruence (j m : Nat) :
    (∃ u v, j=319+512*u ∧
      (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)=574+1024*v ∧
      (u+v)%16=(15+4*u)%16) ↔
    j%512=319 ∧ (3*m+7*j+14025)%16384=0 := by
  constructor
  · rintro ⟨u,v,hj,hk,hsector⟩
    have hm7 := s3_pullback_forces_m_ge7 j m u v hj hk
    have hstop : (574+1024*v)+j+3*m+5 =
        (2:Nat)^(2*m+2)*(j+3) := by
      rw [← hk]
      exact Nat.sub_add_cancel (high_score_nonnegative j m)
    have hpow : 16384 ∣ (2:Nat)^(2*m+2) := by
      have hp : (2:Nat)^14 ∣ (2:Nat)^(2*m+2) :=
        Nat.pow_dvd_pow 2 (by omega)
      simpa only [show (2:Nat)^14=16384 by decide] using hp
    have hprod : 16384 ∣ (2:Nat)^(2*m+2)*(j+3) := by
      obtain ⟨q,hq⟩ := hpow
      refine ⟨q*(j+3),?_⟩
      rw [hq]
      ac_rfl
    have hmod : ((574+1024*v)+j+3*m+5)%16384=0 := by
      rw [hstop]
      exact Nat.mod_eq_zero_of_dvd hprod
    have hjmod : j%512=319 := by
      rw [hj]
      omega
    have htarget : (3*m+7*j+14025)%16384=0 := by
      rw [hj]
      omega
    exact ⟨hjmod,htarget⟩
  · rintro ⟨hjmod,hcong⟩
    let u : Nat := j/512
    have hj : j=319+512*u := by
      dsimp [u]
      have hd := Nat.mod_add_div j 512
      rw [hjmod] at hd
      omega
    have hm512 : m%512=42 := by
      rw [hj] at hcong
      omega
    have hm42 : 42≤m := by omega
    have hm7 : 7≤m := by omega
    let k : Nat := (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)
    have hstop : k+j+3*m+5=(2:Nat)^(2*m+2)*(j+3) := by
      dsimp [k]
      exact Nat.sub_add_cancel (high_score_nonnegative j m)
    have hpow : 16384 ∣ (2:Nat)^(2*m+2) := by
      have hp : (2:Nat)^14 ∣ (2:Nat)^(2*m+2) :=
        Nat.pow_dvd_pow 2 (by omega)
      simpa only [show (2:Nat)^14=16384 by decide] using hp
    have hprod : 16384 ∣ (2:Nat)^(2*m+2)*(j+3) := by
      obtain ⟨q,hq⟩ := hpow
      refine ⟨q*(j+3),?_⟩
      rw [hq]
      ac_rfl
    have hmodStop : (k+j+3*m+5)%16384=0 := by
      rw [hstop]
      exact Nat.mod_eq_zero_of_dvd hprod
    have hmodK : k%16384=(15934+3072*u)%16384 := by
      rw [hj] at hmodStop
      omega
    have hdiv : 1024 ∣ 16384 := by decide
    have hkmod1024 : k%1024=574 := by
      calc
        k%1024 = (k%16384)%1024 :=
          (Nat.mod_mod_of_dvd k hdiv).symm
        _ = ((15934+3072*u)%16384)%1024 := by rw [hmodK]
        _ = (15934+3072*u)%1024 :=
          Nat.mod_mod_of_dvd (15934+3072*u) hdiv
        _ = 574 := by omega
    let v : Nat := k/1024
    have hdecomp : k%1024+1024*(k/1024)=k :=
      Nat.mod_add_div k 1024
    have hk : k=574+1024*v := by
      dsimp [v]
      omega
    have hv16 : v%16=(15+3*u)%16 := by
      rw [hk] at hmodK
      omega
    have hsector : (u+v)%16=(15+4*u)%16 := by omega
    have hk' :
        (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)=574+1024*v := by
      simpa [k] using hk
    exact ⟨u,v,hj,hk',hsector⟩

/-- Add the two disjoint high-stop progressions to the late-fast
    exact C58 predicate. -/
def highAllowedBoth (j m : Nat) : Prop :=
  lateFastHighAllowed j m ∧
  ¬(j=831 ∧ m%16384=9770) ∧
  ¬(j=1855 ∧ m%16384=12842)

/-- The full second strict image family, pulled back through the
    exact high-stop counter, is excluded by the latest C58 predicate. -/
def highAllowedAllS3 (j m : Nat) : Prop :=
  lateFastHighAllowed j m ∧
  ¬(∃ u v, j=319+512*u ∧
    (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)=574+1024*v ∧
    (u+v)%16=(15+4*u)%16)

/-- The same predicate in the exact parameter-only congruence form. -/
theorem highAllowedAllS3_iff_congruence (j m : Nat) :
    highAllowedAllS3 j m ↔
      lateFastHighAllowed j m ∧
      ¬(j%512=319 ∧ (3*m+7*j+14025)%16384=0) := by
  unfold highAllowedAllS3
  constructor
  · rintro ⟨hbase,hnot⟩
    refine ⟨hbase,?_⟩
    intro hcong
    exact hnot ((s3_image_pullback_iff_congruence j m).2 hcong)
  · rintro ⟨hbase,hnot⟩
    refine ⟨hbase,?_⟩
    intro hfamily
    exact hnot ((s3_image_pullback_iff_congruence j m).1 hfamily)

/-- Exact Machine C blank-halting iff after excluding every high-stop
    target in the second strict sixth/seventh image family, not only
    the two explicit progressions. -/
theorem blank_halts_iff_c58_late_fast_all_s3 :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11C58ValSix.lowAllowed m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision
          1 (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedAllS3 j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [blank_halts_iff_c58_late_fast_six_seven]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · let k := (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)
      have hreach : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff (2*j+3) k).mp hroot
      have hnot :
          ¬(∃ u v, j=319+512*u ∧ k=574+1024*v ∧
            (u+v)%16=(15+4*u)%16) := by
        rintro ⟨u,v,hj,hk,hsector⟩
        obtain ⟨time,hrun⟩ := hreach
        have hblank :=
          BB6.Agent4Seven.blank_ne_six_seven_band_s3 u v time hsector
        have hx : 2*j+3=641+1024*u := by omega
        apply hblank
        rw [hx,hk] at hrun
        exact hrun
      exact Or.inr ⟨j,m,⟨hprior,hnot⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

/-- The first explicit progression is removed by the full image-family
    predicate as well as by the two-parameter shorthand. -/
theorem s3_parameter_family_removed_from_all (t : Nat) :
    ¬highAllowedAllS3 831 (9770+16384*t) := by
  intro h
  obtain ⟨v,hkv,hv16⟩ := s3_high_target t
  have hsector : (1+v)%16=(15+4*1)%16 := by omega
  exact h.2 ⟨1,v,by decide,hkv,hsector⟩

/-- The second explicit progression is removed by the full image-family
    predicate as well as by the two-parameter shorthand. -/
theorem s3_second_parameter_family_removed_from_all (t : Nat) :
    ¬highAllowedAllS3 1855 (12842+16384*t) := by
  intro h
  obtain ⟨v,hkv,hv16⟩ := s3_high_target_second t
  have hsector : (3+v)%16=(15+4*3)%16 := by omega
  exact h.2 ⟨3,v,by decide,hkv,hsector⟩

/-- Exact Machine C blank-halting iff after adding both independent
    Agent 4 six/seven source-image exclusions to the latest late-fast
    C58 high predicate. -/
theorem blank_halts_iff_c58_late_fast_six_seven_both :
    BB6.CReachBridge.RunHalts ↔
      (∃ m, BB6.Agent11C58ValSix.lowAllowed m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision
          1 (2^(2*m+3)-(3*m+4))=true) ∨
      (∃ j m, highAllowedBoth j m ∧
        BB6.Agent3ValSix.valSixMixedRootDecision (2*j+3)
          (2^(2*m+2)*(j+3)-(j+3*m+5))=true) := by
  rw [blank_halts_iff_c58_late_fast_six_seven]
  constructor
  · rintro (hlow | ⟨j,m,hprior,hroot⟩)
    · exact Or.inl hlow
    · let k := (2:Nat)^(2*m+2)*(j+3)-(j+3*m+5)
      have hreach : BB6.Agent3.CReach (2*j+3) k :=
        (BB6.Agent3ValSix.valSixMixedRootDecision_iff (2*j+3) k).mp hroot
      have hnot1 : ¬(j=831 ∧ m%16384=9770) := by
        rintro ⟨rfl,hmres⟩
        have hform : m=9770+16384*(m/16384) := by
          have hd := Nat.mod_add_div m 16384
          rw [hmres] at hd
          omega
        dsimp [k] at hreach
        rw [hform] at hreach
        obtain ⟨time,hrun⟩ := hreach
        exact s3_high_parameter_no_blank (m/16384) time hrun
      have hnot2 : ¬(j=1855 ∧ m%16384=12842) := by
        rintro ⟨rfl,hmres⟩
        have hform : m=12842+16384*(m/16384) := by
          have hd := Nat.mod_add_div m 16384
          rw [hmres] at hd
          omega
        dsimp [k] at hreach
        rw [hform] at hreach
        obtain ⟨time,hrun⟩ := hreach
        exact s3_high_parameter_no_blank_second (m/16384) time hrun
      exact Or.inr ⟨j,m,⟨hprior,hnot1,hnot2⟩,hroot⟩
  · rintro (hlow | ⟨j,m,⟨hprior,_⟩,hroot⟩)
    · exact Or.inl hlow
    · exact Or.inr ⟨j,m,hprior,hroot⟩

/-- The first explicit high-stop progression passes all earlier
    C58/late-fast filters but is removed by the new exact predicate. -/
theorem s3_parameter_family_removed (t : Nat) :
    ¬highAllowedBoth 831 (9770+16384*t) := by
  intro h
  exact h.2.1 ⟨by rfl,by omega⟩

/-- The second explicit high-stop progression is also removed. -/
theorem s3_second_parameter_family_removed (t : Nat) :
    ¬highAllowedBoth 1855 (12842+16384*t) := by
  intro h
  exact h.2.2 ⟨by rfl,by omega⟩

#print axioms prior_c58_admits_six_seven_diagonal
#print axioms prior_c58_admits_concrete_infinite_family
#print axioms prior_latefast_admits_six_seven_diagonal
#print axioms prior_latefast_admits_concrete_infinite_family
#print axioms blank_halts_iff_c58_all_depth_six_seven
#print axioms concrete_family_removed
#print axioms blank_halts_iff_c58_late_fast_six_seven
#print axioms latefast_concrete_family_removed
#print axioms prior_latefast_admits_s3_parameter_family
#print axioms blank_halts_iff_c58_late_fast_six_seven_both
#print axioms s3_parameter_family_removed
#print axioms prior_latefast_admits_s3_second_parameter_family
#print axioms prior_latefast_admits_s3_image_family
#print axioms s3_second_parameter_family_removed
#print axioms blank_halts_iff_c58_late_fast_all_s3
#print axioms s3_parameter_family_removed_from_all
#print axioms s3_second_parameter_family_removed_from_all

end BB6.Agent4SevenC58
