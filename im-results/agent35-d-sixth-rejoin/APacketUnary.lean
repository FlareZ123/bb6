import Lean.Elab.Tactic.Omega
import CodeImplicitNil
import PacketSource

set_option maxHeartbeats 20000000
set_option maxRecDepth 55000

namespace BB6.Agent35APacketUnary

open CryptidBoundary
open BB6.Agent31PacketSource
open CryptidA

/-- Code for an A-terminal packet whose unary block has length 3r+1.
    The final 10 token absorbs the delimiter, and the six-one tail is
    represented by two further 111 tokens. -/
def ws (q r : Nat) : List Bool :=
  List.replicate q false ++ List.replicate r true ++ [false,true,true]

def ys : List Bool := false :: List.replicate 6 true

def duration (k q r : Nat) : Nat :=
  (12*k*k+41*k+32) +
    (wordCost (4*k+3) (ws q r) +
      (2*((4*k+3)+wordInc (ws q r))+6))

private theorem code_append (xs ys : List Bool) :
    wordCode (xs++ys) = wordCode xs ++ wordCode ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases b <;> simp [wordCode,ih,List.append_assoc]

private theorem code_true_repeat (n : Nat) :
    wordCode (List.replicate n true) = List.replicate (3*n) true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ,wordCode,ih]
    calc
      [true,true,true] ++ List.replicate (3*n) true =
          List.replicate 3 true ++ List.replicate (3*n) true := by rfl
      _ = List.replicate (3+3*n) true := List.replicate_append_replicate
      _ = List.replicate (3*(n+1)) true := by congr 1; omega

private theorem code_false_repeat (n : Nat) :
    wordCode (List.replicate n false) = pairs n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ,wordCode,pairs,ih]

private theorem inc_append (xs ys : List Bool) :
    wordInc (xs++ys) = wordInc xs + wordInc ys := by
  induction xs with
  | nil => simp [wordInc]
  | cons b xs ih =>
    cases b <;> simp [wordInc,ih,Nat.add_assoc]

private theorem inc_false_repeat (n : Nat) :
    wordInc (List.replicate n false) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 1+wordInc (List.replicate n false)=n+1
    omega

private theorem inc_true_repeat (n : Nat) :
    wordInc (List.replicate n true) = 4*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 4+wordInc (List.replicate n true)=4*(n+1)
    omega

private theorem inc_ws (q r : Nat) :
    wordInc (ws q r) = q+4*r+9 := by
  simp [ws,inc_append,inc_false_repeat,inc_true_repeat,wordInc]

private theorem oppairs_false (q : Nat) :
    oppairs q ++ [false] = false :: pairs q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    change false :: true :: (oppairs q ++ [false]) =
      false :: true :: false :: pairs q
    simpa using congrArg (fun bs : List Bool => false :: true :: bs) ih

private theorem packet_word (q r : Nat) :
    word q (3*r+1) ys = false :: wordCode (ws q r) := by
  calc
    word q (3*r+1) ys =
        (oppairs q ++ [false]) ++
          (List.replicate (3*r+1) true ++ ys) := by
      simp [word,List.append_assoc]
    _ = (false :: pairs q) ++
          (List.replicate (3*r+1) true ++ ys) := by
      rw [oppairs_false]
    _ = false :: (pairs q ++
          (List.replicate (3*r+1) true ++ ys)) := by
      simp [List.append_assoc]
    _ = false :: (wordCode (List.replicate q false) ++
          (wordCode (List.replicate r true) ++
            (wordCode [false] ++ wordCode [true,true]))) := by
      rw [code_false_repeat,code_true_repeat]
      simp [ys,wordCode,List.append_assoc]
    _ = false :: wordCode (ws q r) := by
      simp [ws,code_append,List.append_assoc]

private theorem A_start (k q r : Nat) :
    packet (3*k+3) q (3*r+1) ys =
      init (List.replicate (3*k+1) true ++
        false :: wordCode (ws q r)) := by
  have hn : List.replicate (3*k+3) true =
      true :: true :: List.replicate (3*k+1) true := by
    calc
      _ = List.replicate (2+(3*k+1)) true := by congr 1; omega
      _ = List.replicate 2 true ++ List.replicate (3*k+1) true :=
        (List.replicate_append_replicate).symm
      _ = _ := rfl
  unfold packet
  rw [hn,packet_word]
  simp [init,List.append_assoc]

private theorem A_output (k q r : Nat) :
    (⟨[],false,
      List.replicate (2*((4*k+3)+wordInc (ws q r))+5) true,5⟩ :
      CryptidBoundary.Cfg) =
    DRegularSource.sourceSection ⟨8*k+29+2*q+8*r,0,0⟩ := by
  have hi : wordInc (ws q r) = q+4*r+9 := inc_ws q r
  have hn : 2*((4*k+3)+(q+4*r+9))+5 =
      8*k+29+2*q+8*r := by omega
  have hrepl :
      List.replicate (8*k+29+2*q+8*r) true =
        true :: true :: List.replicate (8*k+27+2*q+8*r) true := by
    have hx : 8*k+29+2*q+8*r =
        2+(8*k+27+2*q+8*r) := by omega
    calc
      _ = List.replicate (2+(8*k+27+2*q+8*r)) true :=
        congrArg (fun n : Nat => List.replicate n true) hx
      _ = List.replicate 2 true ++
          List.replicate (8*k+27+2*q+8*r) true :=
        (List.replicate_append_replicate).symm
      _ = _ := rfl
  rw [hi,hn,hrepl]
  simp [DRegularSource.sourceSection,init,oppairs,
    show (8*k+29+2*q+8*r)-2=8*k+27+2*q+8*r by omega,
    List.append_assoc]

/-- Exact original-source A closure for every packet
    M(3k+3,q,3r+1;0 1^6). It returns to the pure-unary regular section
    L(8k+29+2q+8r,0,0), with no bounded q or r. -/
theorem source_a_packet_unary (k q r : Nat) :
    run (duration k q r) (packet (3*k+3) q (3*r+1) ys) =
      DRegularSource.sourceSection ⟨8*k+29+2*q+8*r,0,0⟩ := by
  rw [A_start]
  exact Eq.trans
    (BB6.Agent32Code.full_A_code_implicit_nil k (ws q r))
    (A_output k q r)

#print axioms source_a_packet_unary
end BB6.Agent35APacketUnary
