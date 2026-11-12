import Lean.Elab.Tactic.Omega
import A110111CodeFirst

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent2AP2PacketBoundary

open CryptidBoundary

def fixedTail : List Bool := false :: List.replicate 6 true

def words (q r : Nat) : List Bool :=
  List.replicate q false ++ List.replicate r true

def ys : List Bool := [true,true,true]

def input (k q r : Nat) : Cfg :=
  ⟨[],false,
    List.replicate (3*k+3) true ++
      CryptidBoundary.oppairs q ++
      List.replicate (3*r+2) true ++ fixedTail,
    5⟩

def endpoint (k q r : Nat) : Cfg :=
  let m := 4*k+3+CryptidA.wordInc (words q r)
  ⟨[],false,
    List.replicate (2*m+5) true ++
      CryptidBoundary.oppairs 3 ++ List.replicate 3 true,
    5⟩

def sourceTime (k q r : Nat) : Nat :=
  let m := 4*k+3+CryptidA.wordInc (words q r)
  (12*k*k+41*k+32) +
    (CryptidA.wordCost (4*k+3) (words q r) + (2*m+24))

private theorem wordCode_append (xs zs : List Bool) :
    CryptidA.wordCode (xs ++ zs) =
      CryptidA.wordCode xs ++ CryptidA.wordCode zs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases b <;>
      simp [CryptidA.wordCode,ih,List.append_assoc]

private theorem wordCode_false_repeat (q : Nat) :
    CryptidA.wordCode (List.replicate q false) =
      CryptidBoundary.pairs q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simp [CryptidA.wordCode,CryptidBoundary.pairs,
      List.replicate_succ,ih,List.append_assoc]

private theorem wordCode_true_repeat (r : Nat) :
    CryptidA.wordCode (List.replicate r true) =
      List.replicate (3*r) true := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp [CryptidA.wordCode,List.replicate_succ,ih,
      List.replicate_add,List.append_assoc]

private theorem words_code (q r : Nat) :
    CryptidA.wordCode (words q r) =
      CryptidBoundary.pairs q ++ List.replicate (3*r) true := by
  rw [words,wordCode_append,wordCode_false_repeat,wordCode_true_repeat]

/-- An A terminal packet with p=2 mod 3 is consumed by the
    original A-code 110111 first-return macro. -/
theorem a_p2_packet_reentry (k q r : Nat) :
    run (sourceTime k q r) (input k q r) =
      endpoint k q r := by
  have hshape :
      input k q r =
        CryptidBoundary.init
          (List.replicate (3*k+1) true ++
            false :: (CryptidA.wordCode (words q r) ++
              BB6.CryptidA110111CodeFirst.packet ys)) := by
    simp [input,fixedTail,words,ys,
      CryptidBoundary.init,CryptidBoundary.oppairs,
      words_code,BB6.CryptidA110111CodeFirst.packet,
      List.replicate_add,List.append_assoc]
  have htail :
      false :: ([true,false,true,false,true] ++ ys) =
        CryptidBoundary.oppairs 3 ++ List.replicate 3 true := by
    decide
  rw [hshape]
  simpa [sourceTime,endpoint,ys,htail,
    BB6.CryptidA110111CodeFirst.packet,
    BB6.CryptidA110111CodeFirst.tail] using
    (BB6.CryptidA110111CodeFirst.full_A_code_110111_first_return
      k (words q r) ys).1

#print axioms a_p2_packet_reentry

end BB6.Agent2AP2PacketBoundary
