import Agent46PhaseCounterCheck
import FastFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13PhasedCounter
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent31Pump.Auto
open BB6Coverage.Agent31Pump.Auto.Counter BB6Coverage.Agent31Pump.Auto.PhaseCounter
def phases (i : Fin 4) : Phase :=
  match i.val with
  | 0 => ⟨5,[true,false],[false,true,false,true,true,true],[true]⟩
  | 1 => ⟨0,[false,false,false],[false,true,false,true,true,true],[]⟩
  | 2 => ⟨0,[false,false,false],[false,true,false,true,true,true],[false,true,true]⟩
  | _ => ⟨0,[false,false,false],[false,true,false,true,true,true],[false,true,false,true,true]⟩
def shape : PhaseCounter.Shape 4 :=
  ⟨[false,true,false,true,false,true,false,true],[false,true,false,true,false,true,true,true],phases,fun i => ⟨(i.val+1)%4,by omega⟩,fun i => if i.val=3 then [false] else []⟩

namespace M0LE
/-- 1RB1LD1RC0LE1LA1RE0RF0LA0RD1RA---0RB -/
def p : PartialMachine := FAR.fromCodes [7,14,11,16,2,19,21,0,13,3,24,5]
def incF : Macro := ⟨([.step] ++ [.right [false] [true,false,true,true,true] [false,true,false,true,false,true,true,true] [true,true,true,true,true,true,true,true] (.lit [false,false]) (.lit [false,true,false,true,false,true,false,true]) 12] ++ List.replicate 19 .step ++ [.left [true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true] [false,true,false,true,false,true,false,true] (.lit [false,false]) (.lit [true,true]) 8] ++ List.replicate 26 .step),20,46⟩
def incA : Macro := ⟨([.right [false] [false,true,false,true,true,true] [false,true,false,true,false,true,true,true] [true,true,true,true,true,true,true,true] (.lit [false,false]) (.lit [false,true,false,true,false,true,false,true]) 12] ++ List.replicate 20 .step ++ [.left [true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true] [false,true,false,true,false,true,false,true] (.lit [false,false]) (.lit [true,true]) 8] ++ List.replicate 26 .step),20,46⟩
def enter : Macro := ⟨([.step] ++ [.right [false] [true,false,true,true,true] [false,true,false,true,false,true,true,true] [true,true,true,true,true,true,true,true] (.lit [false,false]) (.lit [true]) 12] ++ List.replicate 8 .step ++ [.left [true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true] [false,true,false,true,false,true,false,true] (.lit [false,false]) (.lit []) 8] ++ List.replicate 20 .step),20,29⟩
def phase1 : Macro := ⟨([.right [false] [false,true,false,true,true,true] [false,true,false,true,false,true,true,true] [true,true,true,true,true,true,true,true] (.lit [false,false]) (.lit []) 12] ++ List.replicate 12 .step ++ [.left [true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true] [false,true,false,true,false,true,false,true] (.lit [false,false]) (.lit [true]) 8] ++ List.replicate 22 .step),20,34⟩
def phase2 : Macro := ⟨([.right [false] [false,true,false,true,true,true] [false,true,false,true,false,true,true,true] [true,true,true,true,true,true,true,true] (.lit [false,false]) (.lit [false,true,true]) 12] ++ List.replicate 18 .step ++ [.left [true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true] [false,true,false,true,false,true,false,true] (.lit [false,false]) (.lit [true]) 8] ++ List.replicate 24 .step),20,42⟩
def exit : Macro := ⟨([.right [false] [false,true,false,true,true,true] [false,true,false,true,false,true,true,true] [true,true,true,true,true,true,true,true] (.lit [false,false]) (.lit [false,true,false,true,true]) 12] ++ List.replicate 19 .step ++ [.left [true,true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true] [false,true,false,true,false,true,false,true] (.lit [false,false]) (.lit [true]) 8] ++ List.replicate 28 .step),20,47⟩
def normal (i : Fin 4) : Macro := if i.val=0 then incF else incA
def overflow (i : Fin 4) : Macro :=
  match i.val with
  | 0 => enter
  | 1 => phase1
  | 2 => phase2
  | _ => exit
def cert : PhaseCounter.Cert 4 := ⟨shape,32,0,[],normal,overflow⟩
theorem checked : PhaseCounter.Checked p cert := by constructor <;> decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := PhaseCounter.never p cert checked m hm
#print axioms never
end M0LE

namespace M1RB
/-- 1RB1LD1RC1RB1LA1RE0RF0LA0RD1RA---0RB -/
def p : PartialMachine := FAR.fromCodes [7,14,11,7,2,19,21,0,13,3,24,5]
def incF : Macro := ⟨([.step] ++ [.right [false] [true,false,true,true,true] [false,true,false,true,false,true,true,true] [true,true,true,true,true,true,true,true] (.lit [false,false]) (.lit [false,true,false,true,false,true,false,true]) 10] ++ List.replicate 17 .step ++ [.left [true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true] [false,true,false,true,false,true,false,true] (.lit [false,false]) (.lit [true,true]) 8] ++ List.replicate 26 .step),18,44⟩
def incA : Macro := ⟨([.step] ++ [.right [false] [true,false,true,true,true] [false,true,false,true,false,true,true,true] [true,true,true,true,true,true,true,true] (.lit [true,false,false]) (.lit [false,true,false,true,false,true,false,true]) 10] ++ List.replicate 17 .step ++ [.left [true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true] [false,true,false,true,false,true,false,true] (.lit [true,false,false]) (.lit [true,true]) 8] ++ List.replicate 26 .step),18,44⟩
def enter : Macro := ⟨([.step] ++ [.right [false] [true,false,true,true,true] [false,true,false,true,false,true,true,true] [true,true,true,true,true,true,true,true] (.lit [false,false]) (.lit [true]) 10] ++ List.replicate 8 .step ++ [.left [true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true] [false,true,false,true,false,true,false,true] (.lit [false,false]) (.lit []) 8] ++ List.replicate 20 .step),18,29⟩
def phase1 : Macro := ⟨([.step] ++ [.right [false] [true,false,true,true,true] [false,true,false,true,false,true,true,true] [true,true,true,true,true,true,true,true] (.lit [true,false,false]) (.lit []) 10] ++ List.replicate 11 .step ++ [.left [true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true] [false,true,false,true,false,true,false,true] (.lit [true,false,false]) (.lit [true]) 8] ++ List.replicate 22 .step),18,34⟩
def phase2 : Macro := ⟨([.step] ++ [.right [false] [true,false,true,true,true] [false,true,false,true,false,true,true,true] [true,true,true,true,true,true,true,true] (.lit [true,false,false]) (.lit [false,true,true]) 10] ++ List.replicate 13 .step ++ [.left [true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true] [false,true,false,true,false,true,false,true] (.lit [true,false,false]) (.lit [true]) 8] ++ List.replicate 24 .step),18,38⟩
def exit : Macro := ⟨([.step] ++ [.right [false] [true,false,true,true,true] [false,true,false,true,false,true,true,true] [true,true,true,true,true,true,true,true] (.lit [true,false,false]) (.lit [false,true,false,true,true]) 10] ++ List.replicate 16 .step ++ [.left [true,true,true,true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true,true,true] [false,true,false,true,false,true,false,true] (.lit [true,false,false]) (.lit [true]) 8] ++ List.replicate 28 .step),18,45⟩
def normal (i : Fin 4) : Macro := if i.val=0 then incF else incA
def overflow (i : Fin 4) : Macro :=
  match i.val with
  | 0 => enter
  | 1 => phase1
  | 2 => phase2
  | _ => exit
def cert : PhaseCounter.Cert 4 := ⟨shape,32,0,[],normal,overflow⟩
theorem checked : PhaseCounter.Checked p cert := by constructor <;> decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := PhaseCounter.never p cert checked m hm
#print axioms never
end M1RB

namespace ThreePhase
def phases (i : Fin 3) : Phase :=
  match i.val with
  | 0 => ⟨5,[true,false],[false,true,false,true,true,true],[true]⟩
  | 1 => ⟨0,[false,false,false],[false,true,false,true,true,true],[]⟩
  | _ => ⟨0,[false,false,false],[false,true,false,true,true,true],[false,true,true]⟩
def shape : PhaseCounter.Shape 3 :=
  ⟨[false,true,false,true,false,true],[false,true,false,true,true,true],phases,fun i => ⟨(i.val+1)%3,by omega⟩,fun i => if i.val=2 then [false] else []⟩

namespace F0RA
/-- 1RB1LD1RC1RE1LA1RE0RF0LA0RD1RA---0RA -/
def p : PartialMachine := FAR.fromCodes [7,14,11,19,2,19,21,0,13,3,24,1]
def incF : Macro := ⟨([.step] ++ [.right [false] [true,false,true,true,true] [false,true,false,true,true,true] [true,true,true,true,true,true] (.lit [false,false]) (.lit [false,true,false,true,false,true]) 8] ++ List.replicate 15 .step ++ [.left [true,true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true] [false,true,false,true,false,true] (.lit [false,false]) (.lit [true,true]) 6] ++ List.replicate 24 .step),14,40⟩
def incA : Macro := ⟨(List.replicate 3 .step ++ [.right [false] [true,true,true] [false,true,false,true,true,true] [true,true,true,true,true,true] (.lit [true,true,true,false,false]) (.lit [false,true,false,true,false,true]) 8] ++ List.replicate 13 .step ++ [.left [true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true] [false,true,false,true,false,true] (.lit [true,true,true,false,false]) (.lit [true,true]) 6] ++ List.replicate 24 .step),14,40⟩
def enter : Macro := ⟨([.step] ++ [.right [false] [true,false,true,true,true] [false,true,false,true,true,true] [true,true,true,true,true,true] (.lit [false,false]) (.lit [true]) 8] ++ List.replicate 8 .step ++ [.left [true,true,true,true,true,true,true] [] [true,true,true,true,true,true] [false,true,false,true,false,true] (.lit [false,false]) (.lit []) 6] ++ List.replicate 20 .step),14,29⟩
def phase1 : Macro := ⟨(List.replicate 3 .step ++ [.right [false] [true,true,true] [false,true,false,true,true,true] [true,true,true,true,true,true] (.lit [true,true,true,false,false]) (.lit []) 8] ++ List.replicate 9 .step ++ [.left [true,true,true,true,true,true] [] [true,true,true,true,true,true] [false,true,false,true,false,true] (.lit [true,true,true,false,false]) (.lit [true]) 6] ++ List.replicate 22 .step),14,34⟩
def exit : Macro := ⟨(List.replicate 3 .step ++ [.right [false] [true,true,true] [false,true,false,true,true,true] [true,true,true,true,true,true] (.lit [true,true,true,false,false]) (.lit [false,true,true]) 8] ++ List.replicate 12 .step ++ [.left [true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true] [false,true,false,true,false,true] (.lit [true,true,true,false,false]) (.lit [true]) 6] ++ List.replicate 26 .step),14,41⟩
def normal (i : Fin 3) : Macro := if i.val=0 then incF else incA
def overflow (i : Fin 3) : Macro :=
  match i.val with
  | 0 => enter
  | 1 => phase1
  | _ => exit
def cert : PhaseCounter.Cert 3 := ⟨ThreePhase.shape,32,0,[],normal,overflow⟩
theorem checked : PhaseCounter.Checked p cert := by constructor <;> decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := PhaseCounter.never p cert checked m hm
#print axioms never
end F0RA

namespace F0RB
/-- 1RB1LD1RC1RE1LA1RE0RF0LA0RD1RA---0RB -/
def p : PartialMachine := FAR.fromCodes [7,14,11,19,2,19,21,0,13,3,24,5]
def incF : Macro := ⟨(List.replicate 3 .step ++ [.right [false] [true,true,true] [false,true,false,true,true,true] [true,true,true,true,true,true] (.lit [true,true,false,false]) (.lit [false,true,false,true,false,true]) 8] ++ List.replicate 13 .step ++ [.left [true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true] [false,true,false,true,false,true] (.lit [true,true,false,false]) (.lit [true,true]) 6] ++ List.replicate 24 .step),14,40⟩
def incA : Macro := ⟨(List.replicate 3 .step ++ [.right [false] [true,true,true] [false,true,false,true,true,true] [true,true,true,true,true,true] (.lit [true,true,true,false,false]) (.lit [false,true,false,true,false,true]) 8] ++ List.replicate 13 .step ++ [.left [true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true] [false,true,false,true,false,true] (.lit [true,true,true,false,false]) (.lit [true,true]) 6] ++ List.replicate 24 .step),14,40⟩
def enter : Macro := ⟨(List.replicate 3 .step ++ [.right [false] [true,true,true] [false,true,false,true,true,true] [true,true,true,true,true,true] (.lit [true,true,false,false]) (.lit [true]) 8] ++ List.replicate 6 .step ++ [.left [true,true,true,true,true] [] [true,true,true,true,true,true] [false,true,false,true,false,true] (.lit [true,true,false,false]) (.lit []) 6] ++ List.replicate 20 .step),14,29⟩
def phase1 : Macro := ⟨(List.replicate 3 .step ++ [.right [false] [true,true,true] [false,true,false,true,true,true] [true,true,true,true,true,true] (.lit [true,true,true,false,false]) (.lit []) 8] ++ List.replicate 9 .step ++ [.left [true,true,true,true,true,true] [] [true,true,true,true,true,true] [false,true,false,true,false,true] (.lit [true,true,true,false,false]) (.lit [true]) 6] ++ List.replicate 22 .step),14,34⟩
def exit : Macro := ⟨(List.replicate 3 .step ++ [.right [false] [true,true,true] [false,true,false,true,true,true] [true,true,true,true,true,true] (.lit [true,true,true,false,false]) (.lit [false,true,true]) 8] ++ List.replicate 12 .step ++ [.left [true,true,true,true,true,true,true,true,true] [] [true,true,true,true,true,true] [false,true,false,true,false,true] (.lit [true,true,true,false,false]) (.lit [true]) 6] ++ List.replicate 26 .step),14,41⟩
def normal (i : Fin 3) : Macro := if i.val=0 then incF else incA
def overflow (i : Fin 3) : Macro :=
  match i.val with
  | 0 => enter
  | 1 => phase1
  | _ => exit
def cert : PhaseCounter.Cert 3 := ⟨ThreePhase.shape,32,0,[],normal,overflow⟩
theorem checked : PhaseCounter.Checked p cert := by constructor <;> decide
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := PhaseCounter.never p cert checked m hm
#print axioms never
end F0RB
end ThreePhase
end BB6.Agent46Raw13PhasedCounter
