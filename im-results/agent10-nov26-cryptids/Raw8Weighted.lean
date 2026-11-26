module
import all Raw8Counted
import all BusyBeaver.BB6.Halt.M_1RB1LE_0LC1RE_HHH1LD_0RD1LA_0RF1RF_1RA0LB
public import Nov26SourceCore
public import FirstHolePath
public import CryptidsHaltIff

open BusyBeaver
open BusyBeaver.M_1RB1LE_0LC1RE_HHH1LD_0RD1LA_0RF1RF_1RA0LB
open BusyBeaver.M_1RB1LE_0LC1RE_HHH1LD_0RD1LA_0RF1RF_1RA0LB.Counted
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent10Nov26
open BB6Coverage BB6.ConjectureBridge BB6.Agent13BlankDelay BB6.Agent47WeightedHalt BB6.Agent8TNFPath

public section

/-- Ordinary moves, excluding the final undefined query. -/
@[expose] def raw8Ticks : Nat := 127357002621565065257620436683386936787539470067051886613218118511080673366941072419030003169655065867449076569424641011574489482373465883365675526698891984731533897533200967458271672457393649647114596314125471135660566111943361843730621394792642277333936847623104308961000089724168905591219305595735931713864752589517911334410100233581671754237003517860991278921217226890440796227582950616514639336930819296066429511864899248696946158576194825836402868940605014639617724789550009265777033152525606033456073540691727721901256364141236872161550422869463852043401520343212555953181130714885650835768030318277837531565019874900364467386746214009188503718874282272725926187590284697947001726343238522323981475257408390954658553165337971013334254732281910474403685

private theorem raw8_count_matches : prefixCost+topCert.ticks = raw8Ticks := by
  decide +kernel

private theorem raw8_source_score :
    (multiStep target (init []) raw8Ticks).isSome = true ∧
      multiStep target (init []) (raw8Ticks+1) = none := by
  obtain ⟨c,hc,hs⟩ := countedHalt
  rw [raw8_count_matches,target_tm_eq_target] at hc
  rw [target_tm_eq_target] at hs
  change multiStep target (init []) raw8Ticks = some c at hc
  constructor
  · rw [hc]; rfl
  · rw [multiStep_succ',hc]
    exact Option.isNone_iff_eq_none.mp hs

private theorem raw8_sourceRun_eq_iterate (m : ConjectureMachines.Machine 6 2) (n : Nat) :
    sourceRun m n =
      (fun y : Option (ConjectureMachines.Cfg 6 2) =>
        y.bind (ConjectureMachines.step m))^[n] (some ConjectureMachines.init) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sourceRun, Function.iterate_succ_apply', ← ih]

@[expose] def raw8Machine : BB6Coverage.Machine := literal [some ⟨true,true,1⟩, some ⟨true,false,4⟩, some ⟨false,false,2⟩, some ⟨true,true,4⟩, none, some ⟨true,false,3⟩, some ⟨false,true,3⟩, some ⟨true,false,0⟩, some ⟨false,true,5⟩, some ⟨true,true,5⟩, some ⟨true,true,0⟩, some ⟨false,false,1⟩]

theorem raw8_source_eq : toAgent8 BusyBeaver.M_1RB1LE_0LC1RE_HHH1LD_0RD1LA_0RF1RF_1RA0LB.machine = raw8Machine := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl

theorem raw8_score : HaltsAfter raw8Machine raw8Ticks := by
  rw [← raw8_source_eq]
  apply (source_halts_after_iff_agent8_halts_after BusyBeaver.M_1RB1LE_0LC1RE_HHH1LD_0RD1LA_0RF1RF_1RA0LB.machine raw8Ticks).mp
  rw [raw8_sourceRun_eq_iterate,raw8_sourceRun_eq_iterate]
  obtain ⟨h₁,h₂⟩ := raw8_source_score
  change (multiStep BusyBeaver.M_1RB1LE_0LC1RE_HHH1LD_0RD1LA_0RF1RF_1RA0LB.machine.toBB (init []) raw8Ticks).isSome = true at h₁
  change multiStep BusyBeaver.M_1RB1LE_0LC1RE_HHH1LD_0RD1LA_0RF1RF_1RA0LB.machine.toBB (init []) (raw8Ticks+1) = none at h₂
  rw [ConjectureMachines.init_toBB, ConjectureMachines.multiStep_toBB, Option.isSome_map] at h₁
  rw [ConjectureMachines.init_toBB, ConjectureMachines.multiStep_toBB, Option.map_eq_none_iff] at h₂
  exact ⟨h₁,h₂⟩

@[expose] def raw8Path : List (Nat × Slot) := [(1, (1, false)), (2, (2, true)), (3, (3, false)), (4, (3, true)), (6, (1, true)), (7, (4, false)), (8, (5, false)), (15, (4, true)), (21, (0, true)), (23, (5, true))]

theorem raw8_reachable : FirstHolePath (forgetHaltRows raw8Machine) 6 :=
  checked_from_root _ _ (by decide +kernel)

theorem raw8_only_halt (s : Slot) : raw8Machine s = none ↔ s = (2,false) := by
  rcases s with ⟨q,b⟩
  have h : ∀ q : Fin 6, ∀ b : Bool, raw8Machine (q,b) = none ↔ (q,b) = (2,false) := by decide +kernel
  exact h q b

theorem raw8_delays :
    possibleDelays (refine (forgetHaltRows raw8Machine) (2,false) none) 0 = [0] := by decide +kernel

/-- Last-hole lift follows the generic construction of Agent 17's RleWeightedTNF. -/
theorem raw8_lastHole (B : Nat) (hB : raw8Ticks+1 ≤ B) :
    Nonempty (WeightedTNFCertificate B (forgetHaltRows raw8Machine) 6) := by
  have hd : HaltsAfter (weightedTNFDefaultCompletion (forgetHaltRows raw8Machine)) raw8Ticks := by
    rw [forgetHaltRows_defaultCompletion]
    exact raw8_score
  obtain ⟨c,hr,hu⟩ := (weightedTNF_halt_iff_firstHole (forgetHaltRows raw8Machine)
    (forgetHaltRows_noAssignedHalt raw8Machine) raw8Ticks).mp hd
  have hslot : readSlot c = (2,false) := by
    apply (raw8_only_halt (readSlot c)).mp
    cases hs : raw8Machine (readSlot c) with
    | none => rfl
    | some mv => simp [forgetHaltRows,hs] at hu
  have hrest : ∀ s, s ≠ readSlot c → ∃ mv, (forgetHaltRows raw8Machine) s = some (some mv) := by
    intro s hne
    cases hs : raw8Machine s with
    | none => exact False.elim (hne (((raw8_only_halt s).mp hs).trans hslot.symm))
    | some mv => exact ⟨mv, by simp [forgetHaltRows,hs]⟩
  refine ⟨.lastHole (forgetHaltRows_root _ (by rfl)) (forgetHaltRows_tnfSupport _)
    (by decide) hr hu hrest ?_⟩
  intro d hd
  rw [hslot,raw8_delays] at hd
  simp at hd
  subst d
  simpa only [Nat.zero_add] using hB

def raw8_weighted_cert (B : Nat) (hB : raw8Ticks+1 ≤ B) :
    WeightedTNFCertificate B (forgetHaltRows raw8Machine) 6 :=
  .weightedLeaf (forgetHaltRows_root _ (by rfl)) (forgetHaltRows_tnfSupport _)
    (forgetHaltRows_noAssignedHalt _) (by
      obtain ⟨cert⟩ := raw8_lastHole B hB
      exact cert.sound)

theorem raw8_weighted_iff (B : Nat) :
    (∀ m, compatible (forgetHaltRows raw8Machine) m → WeightedBound B m) ↔ raw8Ticks+1 ≤ B := by
  constructor
  · intro h
    have hc := weightedTNFDefaultCompletion_compatible (forgetHaltRows raw8Machine)
    rw [forgetHaltRows_defaultCompletion] at hc
    have hd : 0 ∈ delays (zeroNext raw8Machine) 0 := by decide +kernel
    simpa only [Nat.zero_add] using h raw8Machine hc _ 0 raw8_score hd
  · intro h
    exact (raw8_weighted_cert B h).sound

theorem raw8_under_pow2600 : raw8Ticks+1 ≤ 2^2600 := by decide +kernel

theorem raw8_cover (B : Nat) (hB : 2^2600 ≤ B) :
    Cover (WeightedBound B) (forgetHaltRows raw8Machine) :=
  (raw8_weighted_cert B (Nat.le_trans raw8_under_pow2600 hB)).toCover

#print axioms raw8_score
#print axioms raw8_reachable
#print axioms raw8_weighted_iff
#print axioms raw8_cover
end
end BB6.Agent10Nov26
