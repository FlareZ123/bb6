/- Exact computational theorem with two native_decide trust assumptions.
The standard-axiom-only checker can replace seedRun and pumpRun without
changing the unbounded mathematical argument. -/
import GuardedTail
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent6E0ZeroRF1892Pump
open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent6PadGrowth BB6.Agent6GuardedTail

def p : PartialMachine := fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨true,false,3⟩)
  | 2,true => some (some ⟨false,false,2⟩)
  | 3,false => some (some ⟨true,true,0⟩)
  | 3,true => some (some ⟨false,false,4⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨true,true,2⟩)
  | 5,false => some (some ⟨false,false,3⟩)
  | 5,true => some (some ⟨false,true,3⟩)
  | _,_ => none

def word (s : String) : List Bool := s.toList.map (· == '1')
def seedC0 : Z0 := ⟨0, word "", word ""⟩
def seedC78 : Z0 := ⟨0, word "010110011110011110111101111111101111110011110111101111011110111100111111001111111101111111101111011110111111111100111100111101111111101111111111111111011111111000111111111111011111111111111111111111111111110111111110111111110111111110111111111111111100111101111111111111100111111110111101111001111011110111111111111111100111111001111", word ""⟩
def pumpC0 : Z0 := ⟨0, word "010110011110011110111101111111101111110011110111101111011110111100", word ""⟩
def pumpC32 : Z0 := ⟨0, word "010110011110011110111101111111101111110011110111101111011110111100111111001111111101111111101111011110111111111100111100111101111111111111111111100111111111111111111001111000111111111111", word ""⟩
theorem seedRun : run0 p 39854 seedC0 = some seedC78 := by native_decide
theorem pumpRun : guardedRun p 16148 pumpC0 = some pumpC32 := by native_decide
def P : List Bool := word "010110011110011110111101111111101111110011110111101111011110111100"
def B : List Bool := word "111111001111111101111111101111011110111111111100111100111101111111111111111111100111111111111111111001111000111111111111"
def T : List Bool := word "111111001111111101111111101111011110111111111100111100111101111111101111111111111111011111111000111111111111011111111111111111111111111111110111111110111111110111111110111111111111111100111101111111111111100111111110111101111001111011110111111111111111100111111001111"
def RP : List Bool := word ""
def RQ : List Bool := word ""
def family (k : Nat) : Z0 := ⟨0,P ++ (rep B k ++ T),[]⟩

theorem zerosEq (n : Nat) : EqW (List.replicate n false) [] := by
  intro i
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem seed : Reach p 39854 ⟨0,[],[]⟩ (family 0) := by
  have h : run0 p 39854 ⟨0,[],[]⟩ = some ⟨0,P++T,RP⟩ := seedRun
  apply padRun (exactRun h) (eqZ_refl _)
  exact ⟨rfl,fun _ => rfl,zerosEq 0⟩

theorem period (tail : List Bool) : Reach p 16148 ⟨0,P++tail,[]⟩ ⟨0,P++(B++tail),[]⟩ := by
  have h := guardedRun_append p 16148 tail pumpRun
  change run0 p 16148 ⟨0,P++tail,[]⟩ = some ⟨0,(P++B)++tail,RQ⟩ at h
  rw [List.append_assoc] at h
  exact padRun (exactRun h) (eqZ_refl _) ⟨rfl,fun _ => rfl,zerosEq 0⟩

theorem growth (k : Nat) : Reach p 16148 (family k) (family (k+1)) := by
  simpa only [family,rep.eq_2,List.append_assoc] using period (rep B k++T)

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m :=
  never_of_pad_growth p family 39854 (fun _ => 16148) seed (by intro; decide) growth m hm
#print axioms seedRun
#print axioms pumpRun
#print axioms period
#print axioms never
end BB6.Agent6E0ZeroRF1892Pump
