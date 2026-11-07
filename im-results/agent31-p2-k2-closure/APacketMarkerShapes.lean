import Lean.Elab.Tactic.Omega
import P2K2Shapes

set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

namespace BB6.Agent31APacketMarker
open BB6.Agent31P2K2

/-- A q-pair packet's word after its first zero starts with q 10 tokens. -/
def alt : Nat → List Bool
  | 0 => []
  | q+1 => [true,false] ++ alt q

def code (q r : Nat) : List Bool :=
  List.replicate q false ++ List.replicate r true

def codeTail (q r : Nat) : List Bool := code q r ++ [false,false,false,true]

private theorem triple_code (r : Nat) :
    wordCode (List.replicate r true) = List.replicate (3*r) true := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change [true,true,true] ++ wordCode (List.replicate r true) = _
    rw [ih, show 3*(r+1)=3+3*r by omega,←List.replicate_append_replicate]
    rfl

private theorem code_append (xs ys : List Bool) :
    wordCode (xs ++ ys) = wordCode xs ++ wordCode ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [wordCode,ih]

private theorem code_words (q r : Nat) :
    wordCode (code q r) = alt q ++ List.replicate (3*r) true := by
  induction q with
  | zero => simpa [code,alt] using triple_code r
  | succ q ih =>
    change [true,false] ++ wordCode (code q r) =
       ([true,false] ++ alt q) ++ List.replicate (3*r) true
    rw [ih]
    simp

private theorem triple_inc (r : Nat) :
    wordInc (List.replicate r true) = 4*r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change 4+wordInc (List.replicate r true) = 4*(r+1)
    rw [ih]
    omega

private theorem code_inc (q r : Nat) : wordInc (code q r) = q+4*r := by
  induction q with
  | zero => simpa [code] using triple_inc r
  | succ q ih =>
    change 1+wordInc (code q r)=q+1+4*r
    rw [ih]
    omega

private theorem triple_cost (m r : Nat) :
    wordCost m (List.replicate r true) = 6*m*r+29*r+12*r*r := by
  induction r generalizing m with
  | zero => simp [wordCost]
  | succ r ih =>
    change 6*m+41+wordCost (m+4) (List.replicate r true) = _
    rw [ih]
    simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc]
    omega

private theorem code_cost (m q r : Nat) :
    wordCost m (code q r) = 2*q+6*(m+q)*r+29*r+12*r*r := by
  induction q generalizing m with
  | zero => simpa [code] using triple_cost m r
  | succ q ih =>
    change 2+wordCost (m+1) (code q r) = _
    rw [ih]
    have ha : (m+1)+q=m+(q+1) := by omega
    rw [ha]
    omega

private theorem inc_append (xs ys : List Bool) :
    wordInc (xs ++ ys) = wordInc xs + wordInc ys := by
  induction xs with
  | nil => simp [wordInc]
  | cons b xs ih => cases b <;> simp [wordInc,ih,Nat.add_assoc]

private theorem cost_append (m : Nat) (xs ys : List Bool) :
    wordCost m (xs ++ ys) =
      wordCost m xs + wordCost (m+wordInc xs) ys := by
  induction xs generalizing m with
  | nil => simp [wordCost,wordInc]
  | cons b xs ih =>
    cases b
    · change 2+wordCost (m+1) (xs++ys) =
         (2+wordCost (m+1) xs) + wordCost (m+wordInc (false::xs)) ys
      rw [ih]
      simp only [wordInc]
      ac_rfl
    · change 6*m+41+wordCost (m+4) (xs++ys) =
         (6*m+41+wordCost (m+4) xs) + wordCost (m+wordInc (true::xs)) ys
      rw [ih]
      simp only [wordInc]
      ac_rfl

private theorem tail_inc (q r : Nat) :
    wordInc (codeTail q r)=q+4*r+7 := by
  rw [codeTail,inc_append,code_inc]
  rfl

private theorem tail_cost (m q r : Nat) :
    wordCost m (codeTail q r) =
      (2*q+6*(m+q)*r+29*r+12*r*r) +6+(6*(m+q+4*r+3)+41) := by
  rw [codeTail,cost_append,code_cost,code_inc]
  simp only [wordCost]
  omega

/-- Three all-parameter word-code identities for a packet's fixed marker. -/
theorem split_zero (q r : Nat) :
    alt q ++ (List.replicate (3*r) true ++ marker) =
    wordCode (code q r) ++ [false,true,false,true,false,true,true,true] := by
  rw [code_words]
  simp [marker,List.append_assoc]

theorem split_one (q r : Nat) :
    alt q ++ (List.replicate (3*r+1) true ++ marker) =
    wordCode (codeTail q r) := by
  rw [codeTail,code_append,code_words]
  have hn : 3*r+1=3*r+1 := by rfl
  rw [←List.replicate_append_replicate]
  simp [wordCode,marker,List.append_assoc]

theorem split_two (q r : Nat) :
    alt q ++ (List.replicate (3*r+2) true ++ marker) =
    wordCode (code q r) ++
      [true,true,false,true,false,true,false,true,true,true] := by
  rw [code_words,←List.replicate_append_replicate]
  simp [marker,List.append_assoc]

/-- Exact primitive step counts of the three existing original-source A exits. -/
theorem time_zero (k q r : Nat) :
    let m := 4*k+3
    (12*k*k+41*k+32) +
      (wordCost m (code q r) + (2*(m+wordInc (code q r))+6)) =
      12*k*k+49*k+44+4*q+55*r+24*k*r+6*q*r+12*r*r := by
  dsimp
  rw [code_cost,code_inc]
  have hkr : (4*k)*r=4*(k*r) := by ac_rfl
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,hkr]
  omega

theorem time_two (k q r : Nat) :
    let m := 4*k+3
    (12*k*k+41*k+32) +
      (wordCost m (code q r) + (2*(m+wordInc (code q r))+36)) =
      12*k*k+49*k+74+4*q+55*r+24*k*r+6*q*r+12*r*r := by
  dsimp
  rw [code_cost,code_inc]
  have hkr : (4*k)*r=4*(k*r) := by ac_rfl
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,hkr]
  omega

theorem time_one (k q r : Nat) :
    let m := 4*k+3
    (12*k*k+41*k+32) +
      (wordCost m (codeTail q r) + (2*(m+wordInc (codeTail q r))+6)) =
      12*k*k+73*k+141+10*q+79*r+24*k*r+6*q*r+12*r*r := by
  dsimp
  rw [tail_cost,tail_inc]
  have hkr : (4*k)*r=4*(k*r) := by ac_rfl
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,hkr]
  omega

/-- Unary counts after absorbing the terminal initial 1 in p≡0. -/
theorem out_zero (k q r : Nat) :
    2*(4*k+3+wordInc (code q r))+6=8*k+2*q+8*r+12 := by
  rw [code_inc]
  omega

theorem out_one (k q r : Nat) :
    2*(4*k+3+wordInc (codeTail q r))+5=8*k+2*q+8*r+25 := by
  rw [tail_inc]
  omega

theorem out_two (k q r : Nat) :
    2*(4*k+3+wordInc (code q r))+5=8*k+2*q+8*r+11 := by
  rw [code_inc]
  omega

#print axioms split_zero
#print axioms split_one
#print axioms split_two
#print axioms time_zero
#print axioms time_one
#print axioms time_two
#print axioms out_zero
#print axioms out_one
#print axioms out_two
end BB6.Agent31APacketMarker
