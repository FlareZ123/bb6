import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096

namespace BB6.Agent31P2K2

/-- Original D packet marker that appears after its fixed-tail E,p=2 reset. -/
def marker : List Bool := [false,true,false,true,false,true,true,true]

def wordCode : List Bool → List Bool
  | [] => []
  | false :: ws => [true,false] ++ wordCode ws
  | true :: ws => [true,true,true] ++ wordCode ws

def wordInc : List Bool → Nat
  | [] => 0
  | false :: ws => 1 + wordInc ws
  | true :: ws => 4 + wordInc ws

def wordCost : Nat → List Bool → Nat
  | _, [] => 0
  | m, false :: ws => 2 + wordCost (m+1) ws
  | m, true :: ws => (6*m+41) + wordCost (m+4) ws

private theorem code_append (xs ys : List Bool) :
    wordCode (xs ++ ys) = wordCode xs ++ wordCode ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases b <;> simp [wordCode, ih]

private theorem triple_code (r : Nat) :
    wordCode (List.replicate r true) = List.replicate (3*r) true := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change [true,true,true] ++ wordCode (List.replicate r true) =
      List.replicate (3*(r+1)) true
    rw [ih, show 3*(r+1)=3+3*r by omega]
    rw [←List.replicate_append_replicate]
    rfl

theorem residue_zero_word (u : Nat) :
    List.replicate (2*(3*u)+6) true ++ marker =
       wordCode (List.replicate (2*u+2) true) ++ marker := by
  rw [triple_code]
  have hn : 2*(3*u)+6=3*(2*u+2) := by omega
  rw [hn]

theorem residue_one_word (u : Nat) :
    List.replicate (2*(3*u+1)+6) true ++ marker =
      wordCode (List.replicate (2*u+2) true) ++
      [true,true,false,true,false,true,false,true,true,true] := by
  rw [triple_code]
  have hp : 2*(3*u+1)+6=3*(2*u+2)+2 := by omega
  rw [hp, ←List.replicate_append_replicate]
  simp [marker,List.append_assoc]

theorem residue_two_word (u : Nat) :
    List.replicate (2*(3*u+2)+6) true ++ marker =
      wordCode (List.replicate (2*u+3) true ++
        [false,false,false,true]) := by
  rw [code_append,triple_code]
  have hp : 2*(3*u+2)+6=3*(2*u+3)+1 := by omega
  rw [hp, ←List.replicate_append_replicate]
  simp [marker,wordCode,List.append_assoc]

private theorem triple_inc (r : Nat) :
    wordInc (List.replicate r true) = 4*r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change 4 + wordInc (List.replicate r true) = 4*(r+1)
    rw [ih]
    omega

private theorem triple_cost (m r : Nat) :
    wordCost m (List.replicate r true) =
       6*m*r+29*r+12*r*r := by
  induction r generalizing m with
  | zero => simp [wordCost]
  | succ r ih =>
    change (6*m+41) + wordCost (m+4) (List.replicate r true) =
      6*m*(r+1)+29*(r+1)+12*(r+1)*(r+1)
    rw [ih]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
    omega

private theorem word_inc_tail (r : Nat) :
    wordInc (List.replicate r true ++ [false,false,false,true]) = 4*r+7 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change 4 + wordInc (List.replicate r true ++ [false,false,false,true]) =
      4*(r+1)+7
    rw [ih]
    omega

private theorem word_cost_tail (m r : Nat) :
    wordCost m (List.replicate r true ++ [false,false,false,true]) =
      (6*m*r+29*r+12*r*r) + 6 + (6*(m+4*r+3)+41) := by
  induction r generalizing m with
  | zero => simp [wordCost]; omega
  | succ r ih =>
    change (6*m+41) + wordCost (m+4) (List.replicate r true ++ [false,false,false,true]) = _
    rw [ih]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
    omega

/-- Macro-cost algebra only; correspondence to original-source machines is separate. -/
theorem total_cost_zero (t u : Nat) :
    let ke := 3*t+2
    let ka := 8*t+6
    let m := 4*ka+3
    let r := 2*u+2
    (12*ke*ke+49*ke+68+4*(3*u)) +
    ((12*ka*ka+41*ka+32) +
      (wordCost m (List.replicate r true) +
       (2*(m+wordInc (List.replicate r true))+6))) =
    876*t*t+384*t*u+2219*t+48*u*u+506*u+1430 := by
  dsimp
  rw [triple_cost,triple_inc]
  have h3 : t*(3*t)=3*(t*t) := by ac_rfl
  have h8 : t*(8*t)=8*(t*t) := by ac_rfl
  have h2 : t*(2*u)=2*(t*u) := by ac_rfl
  have hu : u*(2*u)=2*(u*u) := by ac_rfl
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,h3,h8,h2,hu]
  omega

theorem total_cost_one (t u : Nat) :
    let ke := 3*t+2
    let ka := 8*t+6
    let m := 4*ka+3
    let r := 2*u+2
    (12*ke*ke+49*ke+68+4*(3*u+1)) +
    ((12*ka*ka+41*ka+32) +
      (wordCost m (List.replicate r true) +
       (2*(m+wordInc (List.replicate r true))+36))) =
    876*t*t+384*t*u+2219*t+48*u*u+506*u+1464 := by
  dsimp
  rw [triple_cost,triple_inc]
  have h3 : t*(3*t)=3*(t*t) := by ac_rfl
  have h8 : t*(8*t)=8*(t*t) := by ac_rfl
  have h2 : t*(2*u)=2*(t*u) := by ac_rfl
  have hu : u*(2*u)=2*(u*u) := by ac_rfl
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,h3,h8,h2,hu]
  omega

theorem total_cost_two (t u : Nat) :
    let ke := 3*t+2
    let ka := 8*t+6
    let m := 4*ka+3
    let r := 2*u+3
    let ws := List.replicate r true ++ [false,false,false,true]
    (12*ke*ke+49*ke+68+4*(3*u+2)) +
    ((12*ka*ka+41*ka+32) +
      (wordCost m ws + (2*(m+wordInc ws)+6))) =
    876*t*t+384*t*u+2603*t+48*u*u+602*u+2010 := by
  dsimp
  rw [word_cost_tail,word_inc_tail]
  have h3 : t*(3*t)=3*(t*t) := by ac_rfl
  have h8 : t*(8*t)=8*(t*t) := by ac_rfl
  have h2 : t*(2*u)=2*(t*u) := by ac_rfl
  have hu : u*(2*u)=2*(u*u) := by ac_rfl
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,h3,h8,h2,hu]
  omega

#print axioms residue_zero_word
#print axioms residue_one_word
#print axioms residue_two_word
#print axioms total_cost_zero
#print axioms total_cost_one
#print axioms total_cost_two
end BB6.Agent31P2K2
