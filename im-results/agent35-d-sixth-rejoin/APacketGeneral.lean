import Lean.Elab.Tactic.Omega
import A110111CodeFirst
import PacketSource
import DObsSourceCandidate

set_option maxHeartbeats 20000000
set_option maxRecDepth 55000

namespace BB6.Agent35APacketGeneral
open CryptidBoundary
open BB6.Agent31PacketSource
open CryptidA

def ws (q r : Nat) : List Bool :=
  List.replicate q false ++ List.replicate r true

def ys : List Bool := false :: List.replicate 6 true
def zs : List Bool := [true,true,true]

def duration (k q r : Nat) : Nat :=
  (12*k*k+41*k+32) +
    (wordCost (4*k+3) (ws q r) +
      (2*(4*k+3+q+4*r)+24))

theorem code_append (xs ys : List Bool) :
    wordCode (xs++ys) = wordCode xs ++ wordCode ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases b <;> simp [wordCode,ih,List.append_assoc]

private theorem inc_append (xs ys : List Bool) :
    wordInc (xs++ys) = wordInc xs + wordInc ys := by
  induction xs with
  | nil => simp [wordInc]
  | cons b xs ih =>
    cases b <;> simp [wordInc,ih,Nat.add_assoc]

private theorem inc_false (q : Nat) :
    wordInc (List.replicate q false) = q := by
  induction q with
  | zero => rfl
  | succ q ih =>
      change 1+wordInc (List.replicate q false)=q+1
      omega

private theorem inc_true (r : Nat) :
    wordInc (List.replicate r true) = 4*r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      change 4+wordInc (List.replicate r true)=4*(r+1)
      omega

theorem inc_ws (q r : Nat) :
    wordInc (ws q r) = q+4*r := by
  simp [ws,inc_append,inc_false,inc_true]

theorem oppairs_false (q : Nat) :
    oppairs q ++ [false] = false :: wordCode (List.replicate q false) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    change false :: true :: (oppairs q ++ [false]) =
      false :: true :: false :: wordCode (List.replicate q false)
    simpa using congrArg (fun bs : List Bool => false :: true :: bs) ih

private theorem p_suffix (r : Nat) :
    List.replicate (3*r+2) true ++ ys =
    wordCode (List.replicate r true) ++
      BB6.CryptidA110111CodeFirst.packet zs := by
  induction r with
  | zero => decide
  | succ r ih =>
    calc
      List.replicate (3*(r+1)+2) true ++ ys =
          List.replicate 3 true ++
            (List.replicate (3*r+2) true ++ ys) := by
        have hn : 3*(r+1)+2 = 3+(3*r+2) := by omega
        rw [hn]
        rw [(List.replicate_append_replicate (n:=3) (m:=3*r+2) (a:=true)).symm]
        simp [List.append_assoc]
      _ = List.replicate 3 true ++
            (wordCode (List.replicate r true) ++
              BB6.CryptidA110111CodeFirst.packet zs) := by rw [ih]
      _ = wordCode (List.replicate (r+1) true) ++
            BB6.CryptidA110111CodeFirst.packet zs := by rfl

private theorem packet_word (q r : Nat) :
    word q (3*r+2) ys =
      false :: (wordCode (ws q r) ++
        BB6.CryptidA110111CodeFirst.packet zs) := by
  calc
    word q (3*r+2) ys =
        (oppairs q ++ [false]) ++ (List.replicate (3*r+2) true ++ ys) := by
      simp [word,List.append_assoc]
    _ = (false :: wordCode (List.replicate q false)) ++
          (wordCode (List.replicate r true) ++
            BB6.CryptidA110111CodeFirst.packet zs) := by
      rw [oppairs_false,p_suffix]
    _ = false :: (wordCode (ws q r) ++
        BB6.CryptidA110111CodeFirst.packet zs) := by
      simp [ws,code_append,List.append_assoc]

private theorem A_start (k q r : Nat) :
    BB6.Agent31PacketSource.packet (3*k+3) q (3*r+2) ys =
    init (List.replicate (3*k+1) true ++
      false :: (wordCode (ws q r) ++
        BB6.CryptidA110111CodeFirst.packet zs)) := by
  have hn : List.replicate (3*k+3) true =
      true :: true :: List.replicate (3*k+1) true := by
    calc
      _ = List.replicate (2+(3*k+1)) true := by
        congr 1
        omega
      _ = List.replicate 2 true ++ List.replicate (3*k+1) true :=
        (List.replicate_append_replicate).symm
      _ = _ := rfl
  unfold BB6.Agent31PacketSource.packet
  rw [hn,packet_word]
  simp [init,List.append_assoc]

private theorem A_output (k q r : Nat) :
    (⟨[],false,
      List.replicate
        (2*(4*k+3+wordInc (ws q r))+5) true ++
      BB6.CryptidA110111CodeFirst.tail zs,5⟩ : CryptidBoundary.Cfg) =
    DRegularSource.sourceSection ⟨8*k+11+2*q+8*r,3,2⟩ := by
  have hi : wordInc (ws q r) = q+4*r := inc_ws q r
  have ht : BB6.CryptidA110111CodeFirst.tail zs =
      oppairs 3 ++ List.replicate 2 true := by decide
  have hn : 2*(4*k+3+q+4*r)+5 = 8*k+11+2*q+8*r := by omega
  have hrepl : List.replicate (8*k+11+2*q+8*r) true =
      true :: true :: List.replicate (8*k+9+2*q+8*r) true := by
    have hx : 8*k+11+2*q+8*r = 2+(8*k+9+2*q+8*r) := by omega
    calc
      _ = List.replicate (2+(8*k+9+2*q+8*r)) true :=
        congrArg (fun n : Nat => List.replicate n true) hx
      _ = List.replicate 2 true ++ List.replicate (8*k+9+2*q+8*r) true :=
        (List.replicate_append_replicate).symm
      _ = _ := rfl
  rw [hi,hn,ht,hrepl]
  simp [DRegularSource.sourceSection,init,oppairs,
    show (8*k+11+2*q+8*r)-2=8*k+9+2*q+8*r by omega,
    List.append_assoc]

/-- A complete source-machine return for every A-terminating packet family
    M(3k+3,q,3r+2;0 1^6), with genuinely unbounded pair and triple counts.
    This closes the guarded packet normalizer's A-exit sector p mod 3 = 2
    into canonical regular section L(8k+11+2q+8r,3,2).
    Entirely exact original six-state primitive time and F/0 endpoint. -/
theorem source_a_packet_regular (k q r : Nat) :
    run (duration k q r)
      (BB6.Agent31PacketSource.packet (3*k+3) q (3*r+2) ys) =
    DRegularSource.sourceSection ⟨8*k+11+2*q+8*r,3,2⟩ := by
  have hc : duration k q r =
      (12*k*k+41*k+32) +
        (wordCost (4*k+3) (ws q r) +
          (2*(4*k+3+wordInc (ws q r))+24)) := by
    rw [inc_ws q r]
    simp [duration,Nat.add_assoc]
  rw [A_start,hc]
  exact Eq.trans
    (BB6.CryptidA110111CodeFirst.full_A_code_110111_first_return
      k (ws q r) zs).1
    (A_output k q r)

#print axioms inc_ws
#print axioms source_a_packet_regular
end BB6.Agent35APacketGeneral
