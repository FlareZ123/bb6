import ReturnCore
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent3OneLBReturn
open BB6Coverage BB6Coverage.FAR BB6Coverage.Agent13PackedZipper
open BB6.Agent3PackedAudit BB6.Agent31ThreeHole BB6.Agent13BlankDelay

def incWord : Word → Word
  | [] => [true]
  | false::w => true::w
  | true::w => false::incWord w

theorem pack_incWord (w : Word) : pack (incWord w) = pack w + 1 := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b <;> simp [incWord,pack,Bool.toNat,ih] <;> omega

theorem pack_surj (n : Nat) : ∃ w : Word, pack w = n := by
  induction n with
  | zero => exact ⟨[],rfl⟩
  | succ n ih =>
    obtain ⟨w,hw⟩ := ih
    exact ⟨incWord w,by rw [pack_incWord,hw]⟩

abbrev RLE := List (Tok × Nat)
def expand : RLE → List Tok
  | [] => []
  | (t,n)::rs => List.replicate n t ++ expand rs

theorem input_append (ts us : List Tok) (w : Word) :
    input (ts++us) w = input ts (input us w) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [input,ih]

theorem output_append (ts us : List Tok) (w : Word) :
    output (ts++us) w = output ts (output us w) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [output,ih]

theorem left_append (slow : Bool) (ts us : List Tok) :
    leftClock slow (ts++us) = leftClock slow ts + leftClock slow us := by
  induction ts with
  | nil => simp [leftClock]
  | cons t ts ih => cases t <;> simp [leftClock,ih,Nat.add_assoc]

theorem right_append (ts us : List Tok) :
    rightClock (ts++us) = rightClock ts + rightClock us := by
  induction ts with
  | nil => simp [rightClock]
  | cons t ts ih => cases t <;> simp [rightClock,ih] <;> omega

theorem a_input (n : Nat) (w : Word) :
    7 * pack (input (List.replicate n .a) w) + 2 = 8^n * (7*pack w+2) := by
  induction n with
  | zero => simp [input]
  | succ n ih =>
    calc
      _ = 8 * (7 * pack (input (List.replicate n .a) w) + 2) := by
        simp [List.replicate_succ,input,token,List.cons_append,List.nil_append,pack,Bool.toNat,z,o] <;> omega
      _ = _ := by rw [ih,Nat.pow_succ]; ac_rfl

theorem a_output (n : Nat) (w : Word) :
    7 * pack (output (List.replicate n .a) w) + 1 = 8^n * (7*pack w+1) := by
  induction n with
  | zero => simp [output]
  | succ n ih =>
    calc
      _ = 8 * (7 * pack (output (List.replicate n .a) w) + 1) := by
        simp [List.replicate_succ,output,phi,List.cons_append,List.nil_append,pack,Bool.toNat,z,o] <;> omega
      _ = _ := by rw [ih,Nat.pow_succ]; ac_rfl

theorem b_input (n : Nat) (w : Word) :
    pack (input (List.replicate n .b) w) + 1 = 2^n * (pack w+1) := by
  induction n with
  | zero => simp [input]
  | succ n ih =>
    calc
      _ = 2 * (pack (input (List.replicate n .b) w) + 1) := by
        simp [List.replicate_succ,input,token,List.cons_append,List.nil_append,pack,Bool.toNat,z,o] <;> omega
      _ = _ := by rw [ih,Nat.pow_succ]; ac_rfl

theorem b_output (n : Nat) (w : Word) :
    pack (output (List.replicate n .b) w) = 2^n * pack w := by
  induction n with
  | zero => simp [output]
  | succ n ih =>
    calc
      _ = 2 * pack (output (List.replicate n .b) w) := by
        simp [List.replicate_succ,output,phi,pack,Bool.toNat]
      _ = _ := by rw [ih,Nat.pow_succ]; ac_rfl

def inBlock (t : Tok) (n x : Nat) : Nat :=
  match t with
  | .a => (8^n*(7*x+2)-2)/7
  | .b => 2^n*(x+1)-1

def outBlock (t : Tok) (n x : Nat) : Nat :=
  match t with
  | .a => (8^n*(7*x+1)-1)/7
  | .b => 2^n*x

theorem inBlock_correct (t : Tok) (n : Nat) (w : Word) :
    pack (input (List.replicate n t) w) = inBlock t n (pack w) := by
  cases t with
  | a =>
    change _ = (8^n*(7*pack w+2)-2)/7
    rw [← a_input n w]
    omega
  | b =>
    change _ = 2^n*(pack w+1)-1
    rw [← b_input n w]
    omega

theorem outBlock_correct (t : Tok) (n : Nat) (w : Word) :
    pack (output (List.replicate n t) w) = outBlock t n (pack w) := by
  cases t with
  | a =>
    change _ = (8^n*(7*pack w+1)-1)/7
    rw [← a_output n w]
    omega
  | b => exact b_output n w

def inPack : RLE → Nat → Nat
  | [],x => x
  | (t,n)::rs,x => inBlock t n (inPack rs x)

def outPack : RLE → Nat → Nat
  | [],x => x
  | (t,n)::rs,x => outBlock t n (outPack rs x)

theorem inPack_correct (rs : RLE) (w : Word) :
    pack (input (expand rs) w) = inPack rs (pack w) := by
  induction rs with
  | nil => rfl
  | cons p rs ih =>
    rcases p with ⟨t,n⟩
    rw [expand,input_append,inBlock_correct,ih]
    rfl

theorem outPack_correct (rs : RLE) (w : Word) :
    pack (output (expand rs) w) = outPack rs (pack w) := by
  induction rs with
  | nil => rfl
  | cons p rs ih =>
    rcases p with ⟨t,n⟩
    rw [expand,output_append,outBlock_correct,ih]
    rfl

def lUnit (slow : Bool) : Tok → Nat
  | .a => aClock slow
  | .b => 3
def rUnit : Tok → Nat
  | .a => 5
  | .b => 1

theorem left_repeat (slow : Bool) (t : Tok) (n : Nat) :
    leftClock slow (List.replicate n t) = lUnit slow t * n := by
  induction n with
  | zero => simp [leftClock]
  | succ n ih =>
    cases t <;> simp [List.replicate_succ,leftClock,lUnit,ih,Nat.mul_succ,Nat.add_comm]

theorem right_repeat (t : Tok) (n : Nat) :
    rightClock (List.replicate n t) = rUnit t * n := by
  induction n with
  | zero => simp [rightClock]
  | succ n ih =>
    cases t <;> simp [List.replicate_succ,rightClock,rUnit,ih,Nat.mul_succ]

def lCost (slow : Bool) : RLE → Nat
  | [] => 0
  | (t,n)::rs => lUnit slow t*n + lCost slow rs
def rCost : RLE → Nat
  | [] => 0
  | (t,n)::rs => rUnit t*n + rCost rs

theorem left_cost (slow : Bool) (rs : RLE) :
    leftClock slow (expand rs) = lCost slow rs := by
  induction rs with
  | nil => rfl
  | cons p rs ih =>
    rcases p with ⟨t,n⟩
    rw [expand,left_append,left_repeat,ih]
    rfl

theorem right_cost (rs : RLE) :
    rightClock (expand rs) = rCost rs := by
  induction rs with
  | nil => rfl
  | cons p rs ih =>
    rcases p with ⟨t,n⟩
    rw [expand,right_append,right_repeat,ih]
    rfl

def frontNum (n : Nat) : P := ⟨2,2*n,0⟩

theorem frontNum_eq (w : Word) : packedFront w = frontNum (pack w) := by
  simp [packedFront,enc,front,C,frontNum,pack,z,Bool.toNat]

structure Row where
  rs : RLE
  extra : Bool
  tail : Nat

def before (e : Row) : Nat :=
  1+2*inPack e.rs (if e.extra then 6+16*e.tail else 4*e.tail)

def after (e : Row) : Nat :=
  1+4*outPack e.rs (if e.extra then 25+32*e.tail else 5+8*e.tail)

def cost (slow : Bool) (e : Row) : Nat :=
  2+lCost slow e.rs+(6+if e.extra then 4 else 0)+rCost e.rs+4

theorem row_sound (slow : Bool) (e : Row) :
    runP (parent slow) (cost slow e) (frontNum (before e)) =
      some (frontNum (after e)) := by
  obtain ⟨w,hw⟩ := pack_surj e.tail
  rcases e with ⟨rs,b,t⟩
  cases b
  · have h := packed00 slow (expand rs) w
    simp only [retClock,left_cost,right_cost,frontNum_eq,pack,Bool.toNat,inPack_correct,outPack_correct,hw] at h
    simpa [cost,before,after,pack,z,o,Bool.toNat,hw,← Nat.mul_assoc,Nat.mul_add,← Nat.add_assoc] using h
  · have h := packed0110 slow (expand rs) w
    simp only [retClock,left_cost,right_cost,frontNum_eq,pack,Bool.toNat,inPack_correct,outPack_correct,hw] at h
    simpa [cost,before,after,pack,z,o,Bool.toNat,hw,← Nat.mul_assoc,Nat.mul_add,← Nat.add_assoc] using h

-- A checker of adjacent macro states and accumulated primitive step counts.
def replay (slow : Bool) : List Row → Nat → Option (Nat × Nat)
  | [],x => some (0,x)
  | e::es,x =>
    if x = before e then
      (replay slow es (after e)).map (fun y => (cost slow e+y.1,y.2))
    else none

theorem replay_sound (slow : Bool) (es : List Row) (x n y : Nat)
    (h : replay slow es x = some (n,y)) :
    runP (parent slow) n (frontNum x) = some (frontNum y) := by
  induction es generalizing x n y with
  | nil =>
    simp [replay] at h
    obtain ⟨hn,hy⟩ := h
    subst n; subst y; rfl
  | cons e es ih =>
    simp only [replay] at h
    split at h
    · rename_i hx
      subst x
      cases he : replay slow es (after e) with
      | none => simp [he] at h
      | some v =>
        rcases v with ⟨k,z⟩
        simp [he] at h
        obtain ⟨hn,hy⟩ := h
        subst n; subst y
        exact joinP (row_sound slow e) (ih (after e) k z he)
    · simp at h

def stopBefore (rs : RLE) (tail : Nat) : Nat :=
  1+2*inPack rs (14+16*tail)
def stopCost (slow : Bool) (rs : RLE) : Nat := 2+lCost slow rs+3

theorem stop_sound (slow : Bool) (rs : RLE) (tail : Nat) :
    ∃ p, runP (parent slow) (stopCost slow rs) (frontNum (stopBefore rs tail)) = some p
      ∧ readP p = (0,true) := by
  obtain ⟨w,hw⟩ := pack_surj tail
  refine ⟨enc (gate w (codeRev (expand rs) [o])),?_,gate_read _ _⟩
  have h := packed0111 slow (expand rs) w
  simp only [stopClock,left_cost,frontNum_eq,pack,Bool.toNat,inPack_correct,hw] at h
  simpa [stopCost,stopBefore,pack,z,o,Bool.toNat,hw,← Nat.mul_assoc,Nat.mul_add,← Nat.add_assoc] using h

#print axioms row_sound
#print axioms replay_sound
#print axioms stop_sound
end BB6.Agent3OneLBReturn
