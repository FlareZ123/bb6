import Lean.Elab.Tactic.Omega
import P2K2Shapes

set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

namespace BB6.Agent31P2K1Mod9
open BB6.Agent31P2K2

/-- A q=2 packet after its first zero begins with two 10 code tokens. -/
def headTokens : List Bool := [false,false]
def triple (r : Nat) : List Bool := List.replicate r true
def code (r : Nat) : List Bool := headTokens ++ triple r
def codeTail (r : Nat) : List Bool := code r ++ [false,false,false,true]

private theorem triple_code (r : Nat) :
    wordCode (triple r) = List.replicate (3*r) true := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change [true,true,true] ++ wordCode (triple r) = _
    rw [ih, show 3*(r+1)=3+3*r by omega]
    rw [←List.replicate_append_replicate]
    rfl

private theorem headTokensCode (r : Nat) :
    wordCode (code r) = [true,false,true,false] ++ List.replicate (3*r) true := by
  simpa [code,headTokens,wordCode,triple] using (triple_code r)

private theorem wordCode_append (xs ys : List Bool) :
    wordCode (xs ++ ys) = wordCode xs ++ wordCode ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [wordCode,ih]

private theorem tailCode (r : Nat) :
    wordCode (codeTail r) =
      [true,false,true,false] ++ (List.replicate (3*r) true ++
        [true,false,true,false,true,false,true,true,true]) := by
  rw [codeTail,wordCode_append,headTokensCode]
  simp [wordCode]

/-- Three exact suffix identities after two original E macro returns, for all u. -/
theorem word_zero (u : Nat) :
    [true,false,true,false] ++
       (List.replicate (2*(3*u)+3) true ++ marker) =
    wordCode (code (2*u+1)) ++
       (false :: [true,false,true,false,true,true,true]) := by
  rw [headTokensCode]
  have hn : 2*(3*u)+3=3*(2*u+1) := by omega
  rw [hn]
  simp [marker]

theorem word_one (u : Nat) :
    [true,false,true,false] ++
       (List.replicate (2*(3*u+1)+3) true ++ marker) =
    wordCode (code (2*u+1)) ++
       [true,true,false,true,false,true,false,true,true,true] := by
  rw [headTokensCode]
  have hn : 2*(3*u+1)+3=3*(2*u+1)+2 := by omega
  rw [hn, ←List.replicate_append_replicate]
  simp [marker]

theorem word_two (u : Nat) :
    [true,false,true,false] ++
       (List.replicate (2*(3*u+2)+3) true ++ marker) =
    wordCode (codeTail (2*u+2)) := by
  rw [tailCode]
  have hn : 2*(3*u+2)+3=3*(2*u+2)+1 := by omega
  rw [hn, ←List.replicate_append_replicate]
  simp [marker]

private theorem triple_inc (r : Nat) :
    wordInc (triple r) = 4*r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change 4+wordInc (triple r)=4*(r+1)
    rw [ih]
    omega

private theorem triple_cost (m r : Nat) :
    wordCost m (triple r) = 6*m*r+29*r+12*r*r := by
  induction r generalizing m with
  | zero => simp [triple,wordCost]
  | succ r ih =>
    change 6*m+41+wordCost (m+4) (triple r) = _
    rw [ih]
    simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc]
    omega

private theorem codeInc (r : Nat) : wordInc (code r) = 2+4*r := by
  change 1+(1+wordInc (triple r)) = 2+4*r
  rw [triple_inc]
  omega

private theorem codeCost (m r : Nat) :
    wordCost m (code r) = 4+(6*(m+2)*r+29*r+12*r*r) := by
  change 2+(2+wordCost (m+2) (triple r)) = _
  rw [triple_cost]
  omega

private theorem wordInc_append (xs ys : List Bool) :
    wordInc (xs ++ ys) = wordInc xs + wordInc ys := by
  induction xs with
  | nil => simp [wordInc]
  | cons b xs ih => cases b <;> simp [wordInc,ih,Nat.add_assoc]

private theorem tailInc (r : Nat) : wordInc (codeTail r)=2+4*r+7 := by
  rw [codeTail,wordInc_append,codeInc]
  rfl

private theorem wordCost_append (m : Nat) (xs ys : List Bool) :
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

private theorem tailCost (m r : Nat) :
    wordCost m (codeTail r) =
      4+(6*(m+2)*r+29*r+12*r*r)+6+(6*((m+2)+4*r+3)+41) := by
  rw [codeTail,wordCost_append,codeCost,codeInc]
  simp only [wordCost]
  omega

/-- Exact three-source-macro cost polynomial, q=3u. -/
theorem total_zero (s u : Nat) :
    let ke := 9*s+1
    let kb := 24*s+3
    let ka := 64*s+10
    let m := 4*ka+3
    let r := 2*u+1
    (12*ke*ke+49*ke+68+4*(3*u)) +
     ((12*kb*kb+49*kb+58) +
      ((12*ka*ka+41*ka+32) +
        (wordCost m (code r) + (2*(m+wordInc (code r))+6)))) =
       57036*s*s+3072*s*u+23593*s+48*u*u+674*u+2503 := by
  dsimp
  rw [codeCost,codeInc]
  have hs : s*(9*s)=9*(s*s) := by ac_rfl
  have ht : s*(24*s)=24*(s*s) := by ac_rfl
  have hz : s*(64*s)=64*(s*s) := by ac_rfl
  have hu : u*(2*u)=2*(u*u) := by ac_rfl
  have hsu : s*(2*u)=2*(s*u) := by ac_rfl
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,hs,ht,hz,hu,hsu]
  omega

/-- Exact three-source-macro cost polynomial, q=3u+1. -/
theorem total_one (s u : Nat) :
    let ke := 9*s+1
    let kb := 24*s+3
    let ka := 64*s+10
    let m := 4*ka+3
    let r := 2*u+1
    (12*ke*ke+49*ke+68+4*(3*u+1)) +
     ((12*kb*kb+49*kb+58) +
      ((12*ka*ka+41*ka+32) +
        (wordCost m (code r) + (2*(m+wordInc (code r))+36)))) =
       57036*s*s+3072*s*u+23593*s+48*u*u+674*u+2537 := by
  dsimp
  rw [codeCost,codeInc]
  have hs : s*(9*s)=9*(s*s) := by ac_rfl
  have ht : s*(24*s)=24*(s*s) := by ac_rfl
  have hz : s*(64*s)=64*(s*s) := by ac_rfl
  have hu : u*(2*u)=2*(u*u) := by ac_rfl
  have hsu : s*(2*u)=2*(s*u) := by ac_rfl
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,hs,ht,hz,hu,hsu]
  omega

/-- Exact three-source-macro cost polynomial, q=3u+2. -/
theorem total_two (s u : Nat) :
    let ke := 9*s+1
    let kb := 24*s+3
    let ka := 64*s+10
    let m := 4*ka+3
    let r := 2*u+2
    (12*ke*ke+49*ke+68+4*(3*u+2)) +
     ((12*kb*kb+49*kb+58) +
      ((12*ka*ka+41*ka+32) +
        (wordCost m (codeTail r) + (2*(m+wordInc (codeTail r))+6)))) =
       57036*s*s+3072*s*u+26665*s+48*u*u+770*u+3251 := by
  dsimp
  rw [tailCost,tailInc]
  have hs : s*(9*s)=9*(s*s) := by ac_rfl
  have ht : s*(24*s)=24*(s*s) := by ac_rfl
  have hz : s*(64*s)=64*(s*s) := by ac_rfl
  have hu : u*(2*u)=2*(u*u) := by ac_rfl
  have hsu : s*(2*u)=2*(s*u) := by ac_rfl
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,hs,ht,hz,hu,hsu]
  omega

/-- Closed unary output counts, with one terminal 1 absorbed in q=0. -/
theorem output_zero (s u : Nat) :
    let m := 4*(64*s+10)+3
    let r := 2*u+1
    2*(m+wordInc (code r))+6=512*s+16*u+104 := by
  dsimp
  rw [codeInc]
  omega

theorem output_one (s u : Nat) :
    let m := 4*(64*s+10)+3
    let r := 2*u+1
    2*(m+wordInc (code r))+5=512*s+16*u+103 := by
  dsimp
  rw [codeInc]
  omega

theorem output_two (s u : Nat) :
    let m := 4*(64*s+10)+3
    let r := 2*u+2
    2*(m+wordInc (codeTail r))+5=512*s+16*u+125 := by
  dsimp
  rw [tailInc]
  omega

#print axioms word_zero
#print axioms word_one
#print axioms word_two
#print axioms total_zero
#print axioms total_one
#print axioms total_two
#print axioms output_zero
#print axioms output_one
#print axioms output_two

end BB6.Agent31P2K1Mod9
