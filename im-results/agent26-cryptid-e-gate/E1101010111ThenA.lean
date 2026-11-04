import Lean.Elab.Tactic.Omega
import E1101010111Pairs
import ABridgeCode

namespace BB6.Agent26EThenA

open CryptidBoundary
open BB6.Agent26E1101010111

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def afterTail (ys : List Bool) : List Bool :=
  [true,false,true,false,true,false,true,false] ++ ys

/-- The syntactic 111 token code specializes to a long pure-ones word. -/
theorem tripleCode (r : Nat) :
    CryptidA.wordCode (List.replicate r true) =
      List.replicate (3*r) true := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change ([true,true,true] ++
      CryptidA.wordCode (List.replicate r true)) =
      List.replicate (3*(r+1)) true
    rw [ih]
    have ht : 3*(r+1) = 3+3*r := by omega
    rw [ht]
    rw [←List.replicate_append_replicate]
    rfl

/-- For E index k=3t+2, and q=3u, its first F/0 return is
    exactly a source A-section with 2u+2 consecutive 111 tokens. -/
private theorem e_to_a_section (t u : Nat) (ys : List Bool) :
    (⟨[],false,List.replicate (8*(3*t+2)+5) true ++
      bWord (3*u) ys,5⟩ : Cfg) =
    init (List.replicate (3*(8*t+6)+1) true ++
      false :: (CryptidA.wordCode (List.replicate (2*u+2) true) ++
        false :: afterTail ys)) := by
  rw [bWord_shape]
  rw [tripleCode]
  have hcount : 2*(3*u)+6 = 3*(2*u+2) := by omega
  rw [hcount]
  have hrep : List.replicate (8*(3*t+2)+5) true =
      true :: true :: List.replicate (3*(8*t+6)+1) true := by
    have hn : 8*(3*t+2)+5=2+(3*(8*t+6)+1) := by omega
    rw [hn]
    calc
      _ = List.replicate 2 true ++
            List.replicate (3*(8*t+6)+1) true := by
              rw [List.replicate_append_replicate]
      _ = _ := by rfl
  rw [hrep]
  rfl

/-- A second independent symbolic sector: after an E exception with
    k≡2 mod 3, q≡0 mod 3 the NEXT genuine section is an A-code return. -/
theorem e_then_a (t u : Nat) (ys : List Bool) :
    let ke := 3*t+2
    let qe := 3*u
    let ka := 8*t+6
    let ws := List.replicate (2*u+2) true
    let m := 4*ka+3
    let timeE := 12*ke*ke+49*ke+80+4*qe
    let timeA := (12*ka*ka+41*ka+32) +
      (CryptidA.wordCost m ws+(2*(m+CryptidA.wordInc ws)+6))
    run (timeE+timeA)
      (init (List.replicate (3*ke+2) true ++
        false :: (pairs qe ++ wordE ys))) =
      ⟨[],false,List.replicate (2*(m+CryptidA.wordInc ws)+5) true ++
        afterTail ys,5⟩ := by
  dsimp
  rw [run_add, full_E_1101010111_pairs (3*t+2) (3*u) ys]
  rw [e_to_a_section]
  exact BB6.Agent35.full_A_code (8*t+6)
     (List.replicate (2*u+2) true) (afterTail ys)

#print axioms tripleCode
#print axioms e_then_a

end BB6.Agent26EThenA
