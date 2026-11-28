import Raw54Base
import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option autoImplicit false
namespace BB6.Agent8Raw54.OneRDCompact
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay

/-- Raw54 after the next E1=1RD transition. -/
abbrev parent : PartialMachine := refine BB6.Agent8Raw54.raw54 (4,true) (some ⟨true,true,3⟩)

/-- Little-endian base-25 coding of the 12 table slots (0..23 moves; 24 = hole).
    Every encoded row is decoded and checked by Lean, not trusted externally. -/
def fromCode (c : Nat) : PartialMachine := fun s =>
  let digit := (c / 25 ^ (2*s.1.val + s.2.toNat)) % 25
  if digit == 24 then none
  else some (some ⟨digit / 12 == 1, (digit % 12) / 6 == 1, ⟨digit % 6, Nat.mod_lt _ (by decide)⟩⟩)

def parentOK (c : Nat) : Bool :=
  (List.finRange 6).all fun q => [false,true].all fun b =>
    match parent (q,b) with
    | none => true
    | some t => decide (fromCode c (q,b) = some t)

theorem parentOK_sound (c : Nat) (hc : parentOK c = true)
    (m : Machine) (hm : compatible (fromCode c) m) : compatible parent m := by
  intro ⟨q,b⟩ t ht
  have hq := List.all_eq_true.mp hc q (List.mem_finRange q)
  have hb : b ∈ [false,true] := by cases b <;> simp
  have hslot := List.all_eq_true.mp hq b hb
  simp only [parentOK] at hc
  simp [ht] at hslot
  exact hm (q,b) t hslot

private theorem fromTry {d : Nat} (p : PartialMachine) (start : Fin d) (dfa : List (Fin d))
    (h : (fastTryDfa p start dfa).isSome = true)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  cases hz : fastTryDfa p start dfa with
  | none => simp [hz] at h
  | some cert => exact cert.2.1.sound p cert.2.2 m hm

/-- Each case uses the 1-state DFA [0,0] or 2-state DFA [0,1,0,1].
    Eight separate kernel checks keep memory bounded; the sample covers
    disjoint discovered first-hole cylinders (disjointness is not asserted here). -/
def sampleCheck (x : Nat × Bool) : Bool :=
  parentOK x.1 &&
  (if x.2 then (fastTryDfa (fromCode x.1) (0 : Fin 2) ([0,1,0,1] : List (Fin 2))).isSome
   else (fastTryDfa (fromCode x.1) (0 : Fin 1) ([0,0] : List (Fin 1))).isSome)

def samples0 : List (Nat × Bool) :=
  [
    (57872800374793794,false),
    (55870084339840919,false),
    (55679349603497194,false),
    (30979184622856719,true),
    (59589414251762969,false),
    (32123593949216219,true),
    (56728391234372469,true),
    (34031705423747494,false),
    (43663816107341244,false),
    (46620206400309994,false),
    (16102628245841244,false),
    (47097043626888119,true),
    (44808225228278744,false),
    (4658536458903744,false),
    (47573880667794369,false),
    (7996549183263119,false)
  ]
theorem samples0_verified : samples0.all sampleCheck = true := by decide +kernel

def samples1 : List (Nat × Bool) :=
  [
    (54821958187200519,true),
    (27832975091591019,false),
    (59590329652168794,false),
    (2369870658091094,true),
    (47669400833887644,true),
    (31933774642513119,false),
    (43663968744122469,false),
    (38132810072168894,true),
    (38418912425575619,false),
    (32696866566091244,false),
    (54249906136419369,false),
    (44331693285153719,false),
    (56729459408200444,true),
    (6470822943341244,false),
    (44903897933590694,false),
    (2466000990200619,true)
  ]
theorem samples1_verified : samples1.all sampleCheck = true := by decide +kernel

def samples2 : List (Nat × Bool) :=
  [
    (57302274349512569,false),
    (57874478773059719,false),
    (57969846371028469,false),
    (46144284896403744,false),
    (58446683480184594,false),
    (20299710902325619,true),
    (58542050960700494,false),
    (32602109505778744,false),
    (20871915394528419,false),
    (56730069798481869,false),
    (59114255609294369,false),
    (59209622982262594,false),
    (33269681478450619,false),
    (57302426985981744,false),
    (1512479486044344,true),
    (58160733870872394,true)
  ]
theorem samples2_verified : samples2.all sampleCheck = true := by decide +kernel

def samples3 : List (Nat × Bool) :=
  [
    (42425107659950569,false),
    (16675901077950594,false),
    (22874784173731544,true),
    (59591245208903594,false),
    (59591245316340969,false),
    (558805169903619,false),
    (57302579349325294,false),
    (45286283011434644,true),
    (56444272523419369,true),
    (49577817455059994,false),
    (39278134876716244,false),
    (23447141224434994,false),
    (59591397835747344,false),
    (59591397884512969,false),
    (23828611029106544,false),
    (59591397904200469,false)
  ]
theorem samples3_verified : samples3.all sampleCheck = true := by decide +kernel

def samples4 : List (Nat × Bool) :=
  [
    (41280851058513119,false),
    (47002896956731869,false),
    (16867398763403744,false),
    (43665647210638019,true),
    (5614041819934994,true),
    (15436887445200469,false),
    (46622037454778744,false),
    (42330503128903494,false),
    (40041684622778744,false),
    (16199826898372194,true),
    (47289609447184994,false),
    (56826352767575619,false),
    (57303342298450294,false),
    (3420743489934994,true),
    (54823789300481744,true),
    (54823789222403269,true)
  ]
theorem samples4_verified : samples4.all sampleCheck = true := by decide +kernel

def samples5 : List (Nat × Bool) :=
  [
    (3992948236122469,false),
    (32793912581825619,false),
    (50150785150184994,true),
    (35750302845513094,false),
    (49578580550606869,false),
    (7140073245981744,true),
    (50055417542856719,true),
    (53393277826075294,false),
    (54823789115169244,true),
    (56826505355403744,false),
    (15913877191387869,true),
    (25069150628888069,false),
    (42998227777325494,false),
    (55205259027325619,false),
    (17630643324106869,false),
    (45287198538684894,true)
  ]
theorem samples5_verified : samples5.all sampleCheck = true := by decide +kernel

def samples6 : List (Nat × Bool) :=
  [
    (44714993968450619,false),
    (11145658070231869,false),
    (38611478382606869,false),
    (55682248646481869,false),
    (59020108773153269,true),
    (19061154954794219,true),
    (56063718431638044,true),
    (33366269710700444,true),
    (50913877142372494,false),
    (3993100814372494,false),
    (30695981673825519,true),
    (49006528548684994,false),
    (57304105413715969,false),
    (179013909934394,true),
    (57494840150012519,false),
    (560483578121944,false)
  ]
theorem samples6_verified : samples6.all sampleCheck = true := by decide +kernel

def samples7 : List (Nat × Bool) :=
  [
    (57876310003559394,false),
    (57971677425403194,false),
    (58067044681637994,false),
    (58067044857341119,false),
    (46432218070138119,false),
    (58448514485950494,false),
    (15628537835747294,true),
    (58639249388294219,false),
    (20778379066403744,false),
    (44715604466793819,false),
    (18489560785075444,false),
    (59116086429341219,false),
    (20969113783091244,false),
    (59211453861137969,false),
    (32985410326091244,false),
    (7045468939388119,false)
  ]
theorem samples7_verified : samples7.all sampleCheck = true := by decide +kernel

def samples : List (Nat × Bool) :=
  samples0 ++ samples1 ++ samples2 ++ samples3 ++ samples4 ++ samples5 ++ samples6 ++ samples7

theorem samples_verified : samples.all sampleCheck = true := by
  simp only [samples, List.all_append, samples0_verified, samples1_verified, samples2_verified, samples3_verified, samples4_verified, samples5_verified, samples6_verified, samples7_verified, Bool.true_and]

/-- Every total six-state machine extending any of the 128 sampled partial
    tables is nonhalting. This theorem is unconditional in Lean. -/
theorem samples_never (x : Nat × Bool) (hx : x ∈ samples)
    (m : Machine) (hm : compatible (fromCode x.1) m) : NeverHalts m := by
  have h := List.all_eq_true.mp samples_verified x hx
  rcases x with ⟨c,mode⟩
  have hh : parentOK c = true ∧ (if mode then (fastTryDfa (fromCode c) (0 : Fin 2) ([0,1,0,1] : List (Fin 2))).isSome
       else (fastTryDfa (fromCode c) (0 : Fin 1) ([0,0] : List (Fin 1))).isSome) = true := by
     simpa only [sampleCheck, Bool.and_eq_true] using h
  have ht : (if mode then (fastTryDfa (fromCode c) (0 : Fin 2) ([0,1,0,1] : List (Fin 2))).isSome
       else (fastTryDfa (fromCode c) (0 : Fin 1) ([0,0] : List (Fin 1))).isSome) = true := by
     exact hh.2
  cases mode with
  | false => exact fromTry (fromCode c) (0 : Fin 1) ([0,0] : List (Fin 1)) (by simpa using ht) m hm
  | true => exact fromTry (fromCode c) (0 : Fin 2) ([0,1,0,1] : List (Fin 2)) (by simpa using ht) m hm

theorem samples_parent (x : Nat × Bool) (hx : x ∈ samples)
    (m : Machine) (hm : compatible (fromCode x.1) m) : compatible parent m := by
  have h := List.all_eq_true.mp samples_verified x hx
  have hh : parentOK x.1 = true ∧ (if x.2 then (fastTryDfa (fromCode x.1) (0 : Fin 2) ([0,1,0,1] : List (Fin 2))).isSome else (fastTryDfa (fromCode x.1) (0 : Fin 1) ([0,0] : List (Fin 1))).isSome) = true := by
    simpa only [sampleCheck, Bool.and_eq_true] using h
  exact parentOK_sound x.1 hh.1 m hm

theorem samples_length : samples.length = 128 := by decide

#print axioms samples_verified
#print axioms samples_never
#print axioms samples_parent
end BB6.Agent8Raw54.OneRDCompact
