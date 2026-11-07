import Lean.Elab.Tactic.Omega
import PacketSource
import E110111Pairs
import BoundaryBZero

set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

namespace BB6.Agent2PacketP2Reset

open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent37E110111

/-- The right suffix created by the terminal E,p=2 exception. -/
def marker : List Bool := oppairs 3 ++ List.replicate 2 true

private theorem one_prefix (q : Nat) :
    [true,true,true] ++ List.replicate (2*(q+1)) true ++ [true] =
    List.replicate (2*q+6) true := by
  calc
    _ = List.replicate 3 true ++ List.replicate (2*(q+1)) true ++
      List.replicate 1 true := by rfl
    _ = List.replicate (3+2*(q+1)+1) true := by
      rw [List.append_assoc, List.replicate_append_replicate,
        List.replicate_append_replicate]
      simp [Nat.add_assoc]
    _ = _ := by congr 1; omega

private theorem longPacket_shape (q : Nat) :
    BB6.Agent37E110111.longPacket q (List.replicate 3 true) =
    [true,true] ++
      (false :: (List.replicate (2*q+6) true ++ marker)) := by
  have ht :
      BB6.Agent37E110111.longPacket q (List.replicate 3 true) =
        [true,true] ++ (false :: (([true,true,true] ++
          List.replicate (2*(q+1)) true ++ [true]) ++ marker)) := by
    simp [BB6.Agent37E110111.longPacket,marker,oppairs,
      List.append_assoc,List.replicate]
  rw [ht, one_prefix]

private theorem oppairs_false (q : Nat) :
    oppairs q ++ [false] = false :: pairs q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simpa [oppairs,pairs,List.append_assoc] using
      congrArg (fun xs : List Bool => false :: true :: xs) ih

/-- Literal E,p=2 fixed-tail input is precisely the original-source
    110111 six-bit exceptional formula with an untouched three-one tail. -/
theorem e_two_input (k q : Nat) :
    packet (3*k+4) q 2 (false :: List.replicate 6 true) =
      init (List.replicate (3*k+2) true ++
        false :: (pairs q ++
          ([true,true,false,true,true,true] ++ List.replicate 3 true))) := by
  have hn : List.replicate (3*k+4) true =
    true :: true :: List.replicate (3*k+2) true := by
    rw [show 3*k+4=2+(3*k+2) by omega,
      ←List.replicate_append_replicate]
    rfl
  have hw : oppairs q ++
      (false :: (List.replicate 2 true ++
        (false :: List.replicate 6 true))) =
      false :: (pairs q ++
        ([true,true,false,true,true,true] ++ List.replicate 3 true)) := by
    calc
      _ = (oppairs q ++ [false]) ++
        (List.replicate 2 true ++ (false :: List.replicate 6 true)) := by
        simp [List.append_assoc]
      _ = _ := by
        rw [oppairs_false]
        simp [List.replicate,List.append_assoc]
  change
    (⟨[],false,List.replicate (3*k+4) true ++
      (oppairs q ++ (false :: (List.replicate 2 true ++
        (false :: List.replicate 6 true)))),5⟩ : Cfg) =
    ⟨[],false,true :: true ::
      (List.replicate (3*k+2) true ++
        false :: (pairs q ++
          ([true,true,false,true,true,true] ++ List.replicate 3 true))),5⟩
  rw [hn,hw]
  simp [List.cons_append]

/-- The first reset result is another *exact original-source* M-packet,
    with a changed marker. It is not necessarily in regular L. -/
theorem e_two_output (k q : Nat) :
    (⟨[],false,List.replicate (8*k+3) true ++
      BB6.Agent37E110111.longPacket q (List.replicate 3 true),5⟩ : Cfg) =
    packet (8*k+5) 0 (2*q+6) marker := by
  have hn : List.replicate (8*k+5) true =
    List.replicate (8*k+3) true ++ [true,true] := by
    rw [show 8*k+5=(8*k+3)+2 by omega,
      ←List.replicate_append_replicate]
    rfl
  rw [longPacket_shape]
  simp [packet,hn,oppairs,List.append_assoc]

def eTwoTime (k q : Nat) : Nat := 12*k*k+49*k+68+4*q

/-- All k,q literal Cryptid D E,p=2 exceptional source return,
    including exact primitive runtime and full physical marker. -/
theorem e_two_reset (k q : Nat) :
    run (eTwoTime k q)
      (packet (3*k+4) q 2 (false :: List.replicate 6 true)) =
      packet (8*k+5) 0 (2*q+6) marker := by
  rw [e_two_input]
  change
    run (12*k*k+49*k+68+4*q)
      (init (List.replicate (3*k+2) true ++
        false :: (pairs q ++
          ([true,true,false,true,true,true] ++ List.replicate 3 true)))) =
      packet (8*k+5) 0 (2*q+6) marker
  rw [BB6.Agent37E110111.full_E_110111_pairs_raw]
  exact e_two_output k q

#print axioms e_two_reset

/-- A complete B,q=0 source return for every right suffix, retaining the
    arbitrary suffix literally after absorbing p unary ones. -/
theorem b_zero_any (k p : Nat) (ys : List Bool) :
    run (12*k*k+49*k+40)
      (packet (3*k+2) 0 p ys) =
      ⟨[],false,List.replicate (8*k+9+p) true ++ ys,5⟩ := by
  have hn : List.replicate (3*k+2) true =
      true::true::List.replicate (3*k) true := by
    rw [show 3*k+2=2+3*k by omega,
      ←List.replicate_append_replicate]
    rfl
  have hin : packet (3*k+2) 0 p ys =
      init (List.replicate (3*k) true ++
        false :: (List.replicate p true ++ ys)) := by
    simp [packet,word,init,hn,oppairs]
  rw [hin, full_B]
  rw [←List.append_assoc, List.replicate_append_replicate]

/-- When the E,p=2 reset index k is divisible by three, the newly
    created packet is a B,q=0 source whose next return is canonical L.
    This closes an infinite, source-certified exceptional subfamily. -/
theorem e_two_k0_regular (t q : Nat) :
    run (eTwoTime (3*t) q +
      (12*(8*t+1)*(8*t+1)+49*(8*t+1)+40))
      (packet (3*(3*t)+4) q 2 (false::List.replicate 6 true)) =
      BB6.Agent2BoundaryBZero.regularSection
        (64*t+2*q+23) 3 2 := by
  rw [run_add, e_two_reset]
  have hA : 8*(3*t)+5=3*(8*t+1)+2 := by omega
  rw [hA]
  rw [b_zero_any (8*t+1) (2*q+6) marker]
  have hN : 8*(8*t+1)+9+(2*q+6) = 64*t+2*q+23 := by omega
  rw [hN]
  simp [BB6.Agent2BoundaryBZero.regularSection,marker,List.append_assoc]

#print axioms b_zero_any
#print axioms e_two_k0_regular


end BB6.Agent2PacketP2Reset
