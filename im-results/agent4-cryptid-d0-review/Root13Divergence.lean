import Root13Section
import SixthRejoin

import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent37Root13Divergence

open CryptidBoundary BB6.BoundaryPadding BB6.Padding

private def root13Time : Nat :=
  BB6.Agent25FifthRoot.fifthReentryTime +
    DRegular.accumulated 4484 BB6.Agent25SixthRoot.seed

/-- Concatenation law for exact successful DRegular runs and their primitive
    costs. -/
private theorem accumulated_append (n m : Nat) :
    ∀ s t : DRegular.L, DRegular.run n s = some t →
      DRegular.accumulated (n+m) s =
        DRegular.accumulated n s + DRegular.accumulated m t := by
  induction n with
  | zero =>
      intro s t h
      simp [DRegular.run] at h
      cases h
      simp [DRegular.accumulated]
  | succ n ih =>
      intro s t h
      cases hn : DRegular.next s with
      | none =>
          simp [DRegular.run, hn] at h
      | some u =>
          have hu : DRegular.run n u = some t := by
            simpa [DRegular.run, hn] using h
          calc
            DRegular.accumulated ((n+1)+m) s =
                DRegular.duration s + DRegular.accumulated (n+m) u := by
                  rw [show (n+1)+m = (n+m)+1 by omega]
                  simp [DRegular.accumulated, hn]
            _ = DRegular.duration s +
                  (DRegular.accumulated n u + DRegular.accumulated m t) := by
                  rw [ih u t hu]
            _ = DRegular.accumulated (n+1) s +
                  DRegular.accumulated m t := by
                  simp [DRegular.accumulated, hn]
                  rw [← Nat.add_assoc]

theorem root13_time_to_sixth :
    root13Time + DRegular.accumulated 10
      BB6.Agent4Root13Section.root13Section =
    BB6.Agent25SixthRoot.sixthExceptionTime := by
  have hacc := accumulated_append 4484 10
    BB6.Agent25SixthRoot.seed
    BB6.Agent4Root13Section.root13Section
    BB6.Agent4Root13Section.root13Section_exact
  have hacc' :
      DRegular.accumulated 4494 BB6.Agent25SixthRoot.seed =
        DRegular.accumulated 4484 BB6.Agent25SixthRoot.seed +
          DRegular.accumulated 10 BB6.Agent4Root13Section.root13Section := by
    simpa using hacc
  simp [root13Time, BB6.Agent25SixthRoot.sixthExceptionTime,
    hacc', Nat.add_assoc]

/-- The index-31,777 state is not just a model state: the source-certified
    blank root reaches it, and ten more regular transitions reach the
    sixth-exception input. -/
theorem root13_to_sixth_original :
    ObsEq
      (run BB6.Agent25SixthRoot.sixthExceptionTime blank)
      (DRegularSource.sourceSection
        ⟨9*BB6.Agent25SixthRoot.t6+7,4,1⟩) := by
  have hroot :
      ObsEq (run root13Time blank)
        (DRegularSource.sourceSection BB6.Agent4Root13Section.root13Section) := by
    simpa [root13Time] using
      BB6.Agent4Root13Section.root13Section_original
  have hstart :
      BB6.Agent25SixthRoot.seed.a ≥ 8 := by
    simp [BB6.Agent25SixthRoot.seed]
  have hdouble := DRegular.run_double 4484
    BB6.Agent25SixthRoot.seed
    BB6.Agent4Root13Section.root13Section
    hstart BB6.Agent4Root13Section.root13Section_exact
  have hcanon : DRegular.Canon BB6.Agent4Root13Section.root13Section := by
    constructor
    · omega
    · right
      exact BB6.Agent4Root13Section.root13Section_shape.2
  have h := BB6.Agent25RootChain.extend_regular blank root13Time 10
    BB6.Agent4Root13Section.root13Section
    ⟨9*BB6.Agent25SixthRoot.t6+7,4,1⟩ hcanon
    BB6.Agent4Root13Section.root13_to_sixth_exception hroot
  rw [root13_time_to_sixth] at h
  exact h

private theorem e_input (t : Nat) :
    DRegularSource.sourceSection ⟨9*t+7,4,1⟩ =
      init (List.replicate (3*(3*t+1)+2) true ++
        false :: (pairs 3 ++ [true,true])) := by
  have hn : (9*t+7)-2 = 3*(3*t+1)+2 := by omega
  simp only [DRegularSource.sourceSection, init, hn, List.replicate_one]
  rw [List.append_assoc, BB6.Agent25BGeneral.oppairs_last]

private def tail : List Bool := false :: List.replicate 6 true

private def kB (t : Nat) : Nat := (64*t+31)/3
private def bCost (t : Nat) : Nat :=
  12*(kB t)*(kB t)+49*(kB t)+40
private def outputA (t : Nat) : Nat := 8*kB t+10
private def eebCost (t : Nat) : Nat :=
  BB6.Agent32EAll.duration (3*t+1) 3 +
    BB6.Agent31SecondSource.secondCost t + bCost t

private theorem kB_exact (t : Nat) (ht : t % 3 = 2) :
    3*kB t = 64*t+31 := by
  have hmod : (64*t+31)%3=0 := by omega
  dsimp [kB]
  omega

private theorem e_step (t : Nat) :
    ObsEq
      (run (BB6.Agent32EAll.duration (3*t+1) 3)
        (DRegularSource.sourceSection ⟨9*t+7,4,1⟩))
      (BB6.Agent32EAll.output (3*t+1) 3 []) := by
  rw [e_input]
  exact BB6.Agent32EAll.all_e_double_implicit_blank (3*t+1) 3

private theorem finish_is_B (t : Nat) (ht : t%3=2) :
    BB6.Agent31SecondSource.finish t 1 =
      BB6.Agent31PacketSource.packet (3*kB t+2) 2 5 tail := by
  have hk := kB_exact t ht
  have hn : 8*(8*t+3)+9 = 3*kB t+2 := by omega
  unfold BB6.Agent31SecondSource.finish
  simp only [BB6.Agent31PacketSource.packet,
    BB6.Agent31PacketSource.word]
  rw [hn]
  rfl

/-- Exact original-source E/E/B continuation from any L(a,4,1) with
    a=9t+7 and t≡2 mod 3. This exposes the third exceptional macro endpoint. -/
theorem eeb_source (t : Nat) (ht : t%3=2) :
    ObsEq
      (run (eebCost t)
        (DRegularSource.sourceSection ⟨9*t+7,4,1⟩))
      (BB6.Agent31PacketSource.packet (outputA t) 1 5 tail) := by
  have hE := e_step t
  have hmiddle :
      BB6.Agent32EAll.output (3*t+1) 3 [] =
        BB6.Agent31SecondSource.middle t 1 := by
    rfl
  have hS :
      ObsEq
        (run (BB6.Agent31SecondSource.secondCost t)
          (BB6.Agent32EAll.output (3*t+1) 3 []))
        (BB6.Agent31PacketSource.packet (3*kB t+2) 2 5 tail) := by
    rw [hmiddle, BB6.Agent31SecondSource.second_source,
      finish_is_B t ht]
    exact cfgEq_refl _
  have hB :
      ObsEq
        (run (bCost t)
          (BB6.Agent31PacketSource.packet (3*kB t+2) 2 5 tail))
        (BB6.Agent31PacketSource.packet (outputA t) 1 5 tail) := by
    unfold bCost
    rw [BB6.Agent31PacketSource.b_packet (kB t) 1 5 tail]
    exact cfgEq_refl _
  have hES := source_chain
    (BB6.Agent32EAll.duration (3*t+1) 3)
    (BB6.Agent31SecondSource.secondCost t)
    (DRegularSource.sourceSection ⟨9*t+7,4,1⟩)
    (BB6.Agent32EAll.output (3*t+1) 3 [])
    (BB6.Agent31PacketSource.packet (3*kB t+2) 2 5 tail)
    hE hS
  exact source_chain
    (BB6.Agent32EAll.duration (3*t+1) 3 +
      BB6.Agent31SecondSource.secondCost t)
    (bCost t)
    (DRegularSource.sourceSection ⟨9*t+7,4,1⟩)
    (BB6.Agent31PacketSource.packet (3*kB t+2) 2 5 tail)
    (BB6.Agent31PacketSource.packet (outputA t) 1 5 tail)
    hES hB

theorem root_after_macro13_original :
    ObsEq
      (run
        (BB6.Agent25SixthRoot.sixthExceptionTime +
          eebCost BB6.Agent25SixthRoot.t6)
        blank)
      (BB6.Agent31PacketSource.packet
        (outputA BB6.Agent25SixthRoot.t6) 1 5 tail) := by
  have ht : BB6.Agent25SixthRoot.t6%3=2 := by
    have h := BB6.Agent35SixthRoot.true_root_t_mod27
    omega
  exact source_chain
    BB6.Agent25SixthRoot.sixthExceptionTime
    (eebCost BB6.Agent25SixthRoot.t6)
    blank
    (DRegularSource.sourceSection
      ⟨9*BB6.Agent25SixthRoot.t6+7,4,1⟩)
    (BB6.Agent31PacketSource.packet
      (outputA BB6.Agent25SixthRoot.t6) 1 5 tail)
    root13_to_sixth_original
    (eeb_source BB6.Agent25SixthRoot.t6 ht)

/-! ## The external 108-step cylinder after the same 13-macro prefix -/

private def externalT : Nat :=
  (cryptidCylinderC10-7)/9

private def externalSeed (k : Nat) : DRegular.L :=
  ⟨3^108*k+cryptidCylinderC,0,0⟩

private def externalTlift (k : Nat) : Nat :=
  externalT + 3^96*8^10*k

private def externalKB : Nat := kB externalT
private def externalAfter13 : Nat := outputA externalT

theorem externalT_exact :
    9*externalT+7 = cryptidCylinderC10 := by
  decide

theorem externalT_mod27 : externalT%27=2 := by
  decide

private theorem externalT_mod3 : externalT%3=2 := by
  have h := externalT_mod27
  omega

private theorem externalTlift_mod3 (k : Nat) : externalTlift k%3=2 := by
  have hbase := externalT_mod3
  have hdiv : 3 ∣ 3^96*8^10*k := by
    refine ⟨3^95*8^10*k, ?_⟩
    have hcoef : 3^96*8^10 = 3*(3^95*8^10) := by decide
    rw [hcoef, Nat.mul_assoc]
  have hz := Nat.mod_eq_zero_of_dvd hdiv
  unfold externalTlift
  omega

theorem externalAfter13_trace_exact :
    externalAfter13 =
      681262754627324040494547942327349340291066102248547451314 := by
  decide

theorem externalAfter13_mod3 : externalAfter13%3=2 := by
  rw [externalAfter13_trace_exact]

theorem external_checkpoint10_lift (k : Nat) :
    DRegular.run 10 (externalSeed k) =
      some ⟨9*externalTlift k+7,4,1⟩ := by
  unfold externalSeed
  rw [cryptid_first10_affine k]
  have hpow : 3^98 = 9*3^96 := by decide
  have hparam :
      3^98*(8^10*k)+cryptidCylinderC10 =
        9*externalTlift k+7 := by
    calc
      3^98*(8^10*k)+cryptidCylinderC10 =
          9*3^96*(8^10*k)+(9*externalT+7) := by
            rw [← externalT_exact, hpow]
      _ = 9*(externalT + 3^96*8^10*k)+7 := by
            have hprod : 3^96*8^10*k = 3^96*(8^10*k) := by
              rw [Nat.mul_assoc]
            calc
              9*3^96*(8^10*k)+(9*externalT+7) =
                  9*(3^96*(8^10*k))+(9*externalT+7) := by
                    rw [Nat.mul_assoc]
              _ = 9*(3^96*8^10*k)+(9*externalT+7) := by
                    rw [← hprod]
              _ = 9*externalT + 9*(3^96*8^10*k)+7 := by omega
              _ = 9*(externalT+3^96*8^10*k)+7 := by rw [Nat.mul_add]
  rw [hparam]

theorem external_after10_original (k : Nat) :
    ObsEq
      (run (DRegular.accumulated 10 (externalSeed k))
        (DRegularSource.sourceSection (externalSeed k)))
      (DRegularSource.sourceSection
        ⟨9*externalTlift k+7,4,1⟩) := by
  have hcanon : DRegular.Canon (externalSeed k) := by
    constructor
    · simp [externalSeed, cryptidCylinderC]
    · right
      rfl
  have hroot :
      ObsEq
        (run 0 (DRegularSource.sourceSection (externalSeed k)))
        (DRegularSource.sourceSection (externalSeed k)) := by
    simp [CryptidBoundary.run]
    exact cfgEq_refl _
  simpa using
    BB6.Agent25RootChain.extend_regular
      (DRegularSource.sourceSection (externalSeed k)) 0 10
      (externalSeed k) ⟨9*externalTlift k+7,4,1⟩ hcanon
      (external_checkpoint10_lift k) hroot

theorem externalAfter13_lift (k : Nat) :
    outputA (externalTlift k) =
      externalAfter13 + 3^95*8^13*k := by
  have hext : 3*externalKB=64*externalT+31 :=
    kB_exact externalT externalT_mod3
  have htmod : externalTlift k%3=2 :=
    externalTlift_mod3 k
  have hlift : 3*kB (externalTlift k) =
      64*externalTlift k+31 :=
    kB_exact (externalTlift k) htmod
  have hpow96 : 3^96 = 3*3^95 := by decide
  have hkb :
      kB (externalTlift k) =
        externalKB+64*3^95*8^10*k := by
    have hnum :
        64*externalTlift k+31 =
          3*(externalKB+64*3^95*8^10*k) := by
      calc
        64*externalTlift k+31 =
            (64*externalT+31)+64*(3^96*8^10*k) := by
              unfold externalTlift
              rw [Nat.mul_add]
              omega
        _ = 3*externalKB + 3*(64*3^95*8^10*k) := by
              rw [← hext, hpow96]
              simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ = 3*(externalKB+64*3^95*8^10*k) := by
              rw [Nat.mul_add]
    omega
  calc
    outputA (externalTlift k) =
        8*(externalKB+64*3^95*8^10*k)+10 := by
          simp [outputA, hkb]
    _ = externalAfter13+3^95*8^13*k := by
          have hcoef : 8*64*8^10=8^13 := by decide
          have hmul :
              8*(64*3^95*8^10*k)=3^95*8^13*k := by
            calc
              8*(64*3^95*8^10*k) =
                  3^95*(8*64*8^10)*k := by ac_rfl
              _ = 3^95*8^13*k := by rw [hcoef]
          calc
            8*(externalKB+64*3^95*8^10*k)+10 =
                8*externalKB+8*(64*3^95*8^10*k)+10 := by
                  rw [Nat.mul_add]
            _ = externalAfter13+3^95*8^13*k := by
                  dsimp [externalAfter13, externalKB, outputA]
                  rw [hmul]
                  omega

theorem external_after_macro13_original (k : Nat) :
    ObsEq
      (run
        (DRegular.accumulated 10 (externalSeed k) +
          eebCost (externalTlift k))
        (DRegularSource.sourceSection (externalSeed k)))
      (BB6.Agent31PacketSource.packet
        (externalAfter13+3^95*8^13*k) 1 5 tail) := by
  have htmod : externalTlift k%3=2 :=
    externalTlift_mod3 k
  have h := source_chain
    (DRegular.accumulated 10 (externalSeed k))
    (eebCost (externalTlift k))
    (DRegularSource.sourceSection (externalSeed k))
    (DRegularSource.sourceSection
      ⟨9*externalTlift k+7,4,1⟩)
    (BB6.Agent31PacketSource.packet
      (outputA (externalTlift k)) 1 5 tail)
    (external_after10_original k)
    (eeb_source (externalTlift k) htmod)
  simpa [externalAfter13_lift k] using h

theorem root_t_delta :
    BB6.Agent25SixthRoot.t6 =
      externalT + 3*8^10*BB6.Agent4Root13Section.root13P := by
  have hshift := BB6.Agent4Root13Section.root13_first10_exact
  have hroot := BB6.Agent4Root13Section.root13_to_sixth_exception
  have hstate :
      BB6.DRegularShift.shiftNat cryptidCheckpoint10
        (8^10*(3^3*BB6.Agent4Root13Section.root13P)) =
        ⟨9*BB6.Agent25SixthRoot.t6+7,4,1⟩ := by
    have hopt :
        some (BB6.DRegularShift.shiftNat cryptidCheckpoint10
          (8^10*(3^3*BB6.Agent4Root13Section.root13P))) =
        some ⟨9*BB6.Agent25SixthRoot.t6+7,4,1⟩ := by
      calc
        _ = DRegular.run 10 BB6.Agent4Root13Section.root13Section :=
          hshift.symm
        _ = _ := hroot
    exact Option.some.inj hopt
  have ha := congrArg DRegular.L.a hstate
  have hscale :
      8^10*(3^3*BB6.Agent4Root13Section.root13P) =
        27*(8^10*BB6.Agent4Root13Section.root13P) := by
    rw [show 3^3=27 by decide]
    simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  simp [BB6.DRegularShift.shiftNat, cryptidCheckpoint10] at ha
  rw [hscale] at ha
  rw [← externalT_exact] at ha
  omega

theorem root_external_after13_difference :
    outputA BB6.Agent25SixthRoot.t6 =
      externalAfter13 +
        8^13*BB6.Agent4Root13Section.root13P := by
  have ht : BB6.Agent25SixthRoot.t6%3=2 := by
    have h := BB6.Agent35SixthRoot.true_root_t_mod27
    omega
  have hext : externalT%3=2 := externalT_mod3
  have hr := kB_exact BB6.Agent25SixthRoot.t6 ht
  have he := kB_exact externalT hext
  have hkb :
      kB BB6.Agent25SixthRoot.t6 =
        kB externalT +
          64*8^10*BB6.Agent4Root13Section.root13P := by
    have hnum :
        3*kB BB6.Agent25SixthRoot.t6 =
          3*(kB externalT +
            64*8^10*BB6.Agent4Root13Section.root13P) := by
      calc
        3*kB BB6.Agent25SixthRoot.t6 =
            64*BB6.Agent25SixthRoot.t6+31 := hr
        _ = (64*externalT+31) +
              64*(3*8^10*BB6.Agent4Root13Section.root13P) := by
                rw [root_t_delta, Nat.mul_add]
                omega
        _ = 3*kB externalT +
              3*(64*8^10*BB6.Agent4Root13Section.root13P) := by
                rw [← he]
                simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ = 3*(kB externalT +
              64*8^10*BB6.Agent4Root13Section.root13P) := by
                rw [Nat.mul_add]
    omega
  calc
    outputA BB6.Agent25SixthRoot.t6 =
        8*(kB externalT +
          64*8^10*BB6.Agent4Root13Section.root13P)+10 := by
            simp [outputA, hkb]
    _ = externalAfter13 +
        8^13*BB6.Agent4Root13Section.root13P := by
          have hcoef : 8*64*8^10=8^13 := by decide
          have hmul :
              8*(64*8^10*BB6.Agent4Root13Section.root13P) =
                8^13*BB6.Agent4Root13Section.root13P := by
            calc
              8*(64*8^10*BB6.Agent4Root13Section.root13P) =
                  (8*64*8^10)*BB6.Agent4Root13Section.root13P := by ac_rfl
              _ = 8^13*BB6.Agent4Root13Section.root13P := by rw [hcoef]
          calc
            8*(kB externalT +
              64*8^10*BB6.Agent4Root13Section.root13P)+10 =
                8*kB externalT +
                  8*(64*8^10*BB6.Agent4Root13Section.root13P)+10 := by
                    rw [Nat.mul_add]
            _ = externalAfter13 +
                  8^13*BB6.Agent4Root13Section.root13P := by
                    dsimp [externalAfter13, outputA]
                    rw [hmul]
                    omega

theorem root13P_mod3 :
    BB6.Agent4Root13Section.root13P%3=1 := by
  have h := BB6.Agent4Root13Section.root13P_mod2187
  omega

theorem root_after13_mod3 :
    outputA BB6.Agent25SixthRoot.t6%3=1 := by
  rw [root_external_after13_difference]
  have he := externalAfter13_mod3
  have hp := root13P_mod3
  have hpow : 8^13%3=2 := by decide
  have hmul :
      (8^13*BB6.Agent4Root13Section.root13P)%3=2 := by
    rw [Nat.mul_mod, hpow, hp]
  omega

/-- The authentic root and the external cylinder have the same 15-bit suffix
    after macro 13; the unary parameters differ by exactly 8^13*p. -/
theorem root_suffix_matches_external :
    BB6.Agent31PacketSource.word 1 5 tail =
      [false,true,false,true,true,true,true,true,
       false,true,true,true,true,true,true] := by
  decide

/-- The external 108-step halting cylinder, propagated through the same
    13-macro prefix, has residual parameter
    C13 + 3^95*8^13*k for arbitrary k. -/
theorem root_not_in_external_residual_cylinder (k : Nat) :
    outputA BB6.Agent25SixthRoot.t6 ≠
      externalAfter13+3^95*8^13*k := by
  intro h
  have hmod := congrArg (fun n : Nat => n%3) h
  have hroot := root_after13_mod3
  have hext := externalAfter13_mod3
  have hdiv : 3 ∣ 3^95*8^13*k := by
    refine ⟨3^94*8^13*k, ?_⟩
    have hcoef : 3^95*8^13 = 3*(3^94*8^13) := by decide
    rw [hcoef, Nat.mul_assoc]
  have hz := Nat.mod_eq_zero_of_dvd hdiv
  omega

/-- Designated section-index bookkeeping used by check_root17.py. The +2
    terms count the two exceptional source-macro endpoints at each reentry;
    these are not primitive machine steps or a first-return minimality claim. -/
theorem root13Section_designated_index :
    8394+2+1026+2+2665+2+10946+2+4252+2+4484 = 31777 := by
  decide

theorem sixthException_designated_index :
    8394+2+1026+2+2665+2+10946+2+4252+2+4494 = 31787 := by
  decide

#print axioms root13_to_sixth_original
#print axioms eeb_source
#print axioms root_after_macro13_original
#print axioms external_after_macro13_original
#print axioms root_external_after13_difference
#print axioms root_not_in_external_residual_cylinder

end BB6.Agent37Root13Divergence
