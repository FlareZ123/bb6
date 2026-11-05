import Lean.Elab.Tactic.Omega
import PacketSource
import ABridgeCode

set_option maxHeartbeats 10000000
set_option maxRecDepth 15000
set_option linter.unusedSimpArgs false

namespace BB6.Agent25AllDepthA
open CryptidBoundary BB6.Agent31PacketSource

def kIndex (m u : Nat) : Nat := 4*3^m*u-1
def eCost (m u q : Nat) : Nat :=
  12*kIndex m u*kIndex m u+49*kIndex m u+58+6*q

def ladderCost : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | m+1, u, q => eCost m u q + ladderCost m (8*u) (q+2)

private theorem pow_pos (m u : Nat) (hu : 0<u) : 0 < 4*3^m*u := by
  exact Nat.mul_pos (Nat.mul_pos (by omega) (Nat.pow_pos (by omega : 0 < 3))) hu

private theorem first_index (m u : Nat) (hu : 0<u) :
    4*3^(m+1)*u+1 = 3*(kIndex m u)+4 := by
  have hp : 4*3^(m+1)*u = 3*(4*3^m*u) := by
    simp only [Nat.pow_succ]
    ac_rfl
  have hpos : 0<4*3^m*u := pow_pos m u hu
  dsimp [kIndex]
  omega

private theorem first_output (m u : Nat) (hu : 0<u) :
    8*(kIndex m u)+9 = 4*3^m*(8*u)+1 := by
  have hpos : 0<4*3^m*u := pow_pos m u hu
  have hh : 8*(4*3^m*u) = 4*3^m*(8*u) := by ac_rfl
  dsimp [kIndex]
  omega

private theorem last_output (m u : Nat) :
    4*8^m*(8*u)+1 = 4*8^(m+1)*u+1 := by
  simp only [Nat.pow_succ]
  ac_rfl

/-- Source-original all-parameter E-packet ladder: m consecutive E steps,
    with all intervening counter divisibilities proved arithmetically.
    The untouched right tail is arbitrary, and m is unbounded. -/
theorem e_ladder (m : Nat) :
    ∀ u q d, 0<u →
      ∀ (ys : List Bool),
        run (ladderCost m u q)
          (packet (4*3^m*u+1) q (3*(m+d)) ys) =
        packet (4*8^m*u+1) (q+2*m) (3*d) ys := by
  induction m with
  | zero =>
    intro u q d hu ys
    simp [ladderCost, CryptidBoundary.run]
  | succ m ih =>
    intro u q d hu ys
    have hn := first_index m u hu
    have ho := first_output m u hu
    have hp : 3*(m+1+d)=3*(m+d)+3 := by omega
    have hfirst :
        run (eCost m u q)
          (packet (4*3^(m+1)*u+1) q (3*(m+1+d)) ys) =
        packet (4*3^m*(8*u)+1) (q+2) (3*(m+d)) ys := by
      simpa only [eCost, hn, ho, hp] using
        (e_packet (kIndex m u) q (3*(m+d)) ys)
    have hu8 : 0<8*u := Nat.mul_pos (by omega) hu
    have hlast := last_output m u
    have hq : (q+2)+2*m=q+2*(m+1) := by omega
    change run (eCost m u q+ladderCost m (8*u) (q+2))
      (packet (4*3^(m+1)*u+1) q (3*(m+1+d)) ys) =
      packet (4*8^(m+1)*u+1) (q+2*(m+1)) (3*d) ys
    rw [run_add, hfirst]
    simpa only [hlast, hq] using ih (8*u) (q+2) d hu8 ys

def words (m d : Nat) : List Bool :=
  List.replicate (2*m) false ++ List.replicate d true

def finalK (m u : Nat) : Nat := (4*8^m*u+1-3)/3

def finalCost (m u d : Nat) : Nat :=
  (12*finalK m u*finalK m u+41*finalK m u+32) +
  (CryptidA.wordCost (4*finalK m u+3) (words m d) +
    (2*(4*finalK m u+3+CryptidA.wordInc (words m d))+6))

private theorem code_append (a b : List Bool) :
    CryptidA.wordCode (a ++ b) =
    CryptidA.wordCode a ++ CryptidA.wordCode b := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    cases x <;> simp only [List.cons_append,CryptidA.wordCode,ih,List.append_assoc]

private theorem code_false (q : Nat) :
    CryptidA.wordCode (List.replicate q false) = pairs q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simp only [List.replicate_succ,CryptidA.wordCode,ih,pairs]
    rfl

private theorem code_true (q : Nat) :
    CryptidA.wordCode (List.replicate q true) =
      List.replicate (3*q) true := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simp only [List.replicate_succ,CryptidA.wordCode,ih]
    calc
      [true,true,true] ++ List.replicate (3*q) true =
        List.replicate (3+3*q) true := by
          simpa only [List.replicate_succ, List.replicate_zero, List.nil_append]
            using (List.replicate_append_replicate (n:=3) (m:=3*q) (a:=true))
      _ = List.replicate (3*(q+1)) true := by congr 1; omega

private theorem code_words (m d : Nat) :
    CryptidA.wordCode (words m d) =
      pairs (2*m) ++ List.replicate (3*d) true := by
  simp [words, code_append,code_false,code_true]

private theorem oppairs_to_pairs (q : Nat) (ys : List Bool) :
    oppairs q ++ false :: ys = false :: (pairs q ++ ys) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simpa [oppairs,pairs,List.append_assoc] using
      congrArg (List.cons false ∘ List.cons true) ih

private theorem final_index (m u : Nat) (hu : 0<u)
    (hmod : (4*8^m*u+1)%3=0) :
    4*8^m*u+1 = 3*finalK m u+3 := by
  have hp : 0<8^m := Nat.pow_pos (by omega)
  have hl : 3 ≤ 4*8^m*u+1 := by
    have hr : 0<4*8^m*u := Nat.mul_pos (Nat.mul_pos (by omega) hp) hu
    omega
  dsimp [finalK]
  omega

private theorem final_as_A (m u d : Nat) (hu : 0<u)
    (hmod : (4*8^m*u+1)%3=0) (ys : List Bool) :
    packet (4*8^m*u+1) (2*m) (3*d) (false::ys) =
      init (List.replicate (3*finalK m u+1) true ++
        false :: (CryptidA.wordCode (words m d) ++ (false::ys))) := by
  have hn := final_index m u hu hmod
  have hr : List.replicate (3*finalK m u+3) true =
      true::true::List.replicate (3*finalK m u+1) true := by
    rw [show 3*finalK m u+3 = ((3*finalK m u+1)+1)+1 by omega]
    rw [List.replicate_succ, List.replicate_succ]
  have hc := code_words m d
  simp [packet, word, hn, hr, init, hc, oppairs_to_pairs,
    List.append_assoc]

private def ys : List Bool := List.replicate 6 true

def output (m u d : Nat) : Cfg :=
  ⟨[],false,List.replicate
    (2*(4*finalK m u+3+CryptidA.wordInc (words m d))+5) true ++ ys,5⟩

private theorem final_A (m u d : Nat) (hu : 0<u)
    (hmod : (4*8^m*u+1)%3=0) :
    run (finalCost m u d)
      (packet (4*8^m*u+1) (2*m) (3*d) (false::ys)) =
      output m u d := by
  rw [final_as_A m u d hu hmod]
  exact BB6.Agent35.full_A_code (finalK m u) (words m d) ys

/-- A source-connected UNBOUNDED family of E^m/A returns, from a
    physically blank-left F/0 input. The full right suffix after the
    packet is exactly six ones and the output is pure unary.
    Requires a final A-congruence and u>0; synthetic-input theorem. -/
theorem all_depth_E_then_A (m u d : Nat) (hu : 0<u)
    (hmod : (4*8^m*u+1)%3=0) :
    run (ladderCost m u 0 + finalCost m u d)
      (packet (4*3^m*u+1) 0 (3*(m+d)) (false::ys)) =
      output m u d := by
  rw [run_add, e_ladder m u 0 d hu (false::ys)]
  simpa only [Nat.zero_add] using final_A m u d hu hmod

#print axioms e_ladder
#print axioms all_depth_E_then_A
end BB6.Agent25AllDepthA
