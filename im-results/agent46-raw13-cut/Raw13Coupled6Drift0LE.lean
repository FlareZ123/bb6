import SweepPumping
import FastFAR
open BB6Coverage BB6Coverage.Agent31Pump
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent46Raw13Coupled6Drift0LE
def p := FAR.fromCodes [7,14,11,24,2,19,18,0,23,16,3,21]
def pre : List Bool := [false,true,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false]
def block : List Bool := [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,false,false,false,false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,false]
def tail : List Bool := [false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true,false,false,false,false,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,false,true,true]
def family (n : Nat) : Z0 := ⟨0,[],pre ++ rep block n ++ tail⟩
theorem seed : run0 p 4235 ⟨0,[],[]⟩ = some (family 0) := by rfl
theorem pump (R : List Bool) : run0 p 4214 ⟨0,[],pre ++ R⟩ = some ⟨0,[],pre ++ block ++ R⟩ := by rfl
theorem grow (n : Nat) : run0 p 4214 (family n) = some (family (n+1)) := by
  simpa only [family,rep,List.append_assoc] using pump (rep block n ++ tail)
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  never_of_growth p family 4235 (fun _ => 4214) seed (fun _ => by decide) grow m hm
#print axioms never
end BB6.Agent46Raw13Coupled6Drift0LE
