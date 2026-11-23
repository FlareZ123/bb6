import Lean.Elab.Tactic.Omega
import ACanonicalTwoTailFirst
import AImplicitOneTailFirstReturn

/-!
# Original canonical A residue b ≡ 0 (mod 3) after positive alternating pairs

For every k,q,r≥0, canonical A section L(3k+3,q+1,3r)
returns with exactly the mixed-code primitive clock, at its first
re-entry into control state F (not just its first blank-left return).
In particular this includes arbitrarily long 01 and 111 token blocks.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

namespace BB6.Agent4ACanonicalOneTail

open CryptidBoundary
open BB6.Agent4AImplicitOne
open BB6.Agent4ACanonicalTwoTail

def tokens0 (q r : Nat) : List Bool :=
  List.replicate q false ++ List.replicate r true

theorem codeTokens0 (q r : Nat) :
    CryptidA.wordCode (tokens0 q r) =
      pairs q ++ List.replicate (3*r) true := by
  unfold tokens0
  rw [codeAppend,codeFalse,codeTrue]

theorem incTokens0 (q r : Nat) :
    CryptidA.wordInc (tokens0 q r) = q+4*r := by
  simp [tokens0,incAppend,incFalse,incTrue]

private theorem onesSnoc (n : Nat) :
    true :: List.replicate n true =
      List.replicate n true ++ [true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact congrArg (List.cons true) ih

/-- Canonical suffix 0(10)^q 1^(3r+1) is a mixed A token word followed
by a single one, with the final zero supplied by the physical blank tape. -/
theorem tokenWord0 (q r : Nat) :
    oppairs (q+1) ++ List.replicate (3*r) true =
      false :: (CryptidA.wordCode (tokens0 q r) ++ [true]) := by
  calc
    oppairs (q+1) ++ List.replicate (3*r) true =
        false :: ((pairs q ++ [true]) ++
          List.replicate (3*r) true) := by
        change (false :: (true :: oppairs q)) ++
            List.replicate (3*r) true = _
        rw [BB6.AOneSource.one_oppairs]
        rfl
    _ = false :: (pairs q ++
          (true :: List.replicate (3*r) true)) := by
        simp [List.append_assoc]
    _ = false :: ((pairs q ++ List.replicate (3*r) true) ++
          [true]) := by
        rw [onesSnoc]
        simp [List.append_assoc]
    _ = false :: (CryptidA.wordCode (tokens0 q r) ++ [true]) := by
        rw [codeTokens0]

private theorem sourceEq (k q r : Nat) :
    DRegularSource.sourceSection ⟨3*k+3,q+1,3*r⟩ =
      oneStart k (tokens0 q r) := by
  have hn : (3*k+3)-2 = 3*k+1 := by omega
  simp only [DRegularSource.sourceSection,oneStart,hn,
    List.append_assoc]
  rw [tokenWord0]

private theorem endEq (k q r : Nat) :
    oneEnd k (tokens0 q r) =
      DRegularSource.sourceSection ⟨8*k+13+2*q+8*r,0,0⟩ := by
  have hn : (8*k+13+2*q+8*r)-2 = 8*k+11+2*q+8*r := by omega
  have hrep :
      List.replicate (8*k+13+2*q+8*r) true =
        true :: true :: List.replicate (8*k+11+2*q+8*r) true := by
    calc
      _ = List.replicate (2+(8*k+11+2*q+8*r)) true := by
        congr 1
        omega
      _ = List.replicate 2 true ++
          List.replicate (8*k+11+2*q+8*r) true :=
          (List.replicate_append_replicate).symm
      _ = _ := rfl
  have htime :
      2*(4*k+3+(q+4*r))+7 = 8*k+13+2*q+8*r := by omega
  change
    (⟨[],false,List.replicate
      (2*(4*k+3+CryptidA.wordInc (tokens0 q r))+7) true,5⟩ : Cfg) =
    DRegularSource.sourceSection ⟨8*k+13+2*q+8*r,0,0⟩
  rw [incTokens0,htime,hrep]
  simp [DRegularSource.sourceSection,hn,oppairs,init]

theorem canonical_A_one_first (k q r : Nat) :
    run (oneCost k (tokens0 q r))
      (DRegularSource.sourceSection ⟨3*k+3,q+1,3*r⟩) =
        DRegularSource.sourceSection ⟨8*k+13+2*q+8*r,0,0⟩ ∧
    ∀ t, 0<t → t<oneCost k (tokens0 q r) →
      (run t (DRegularSource.sourceSection ⟨3*k+3,q+1,3*r⟩)).st ≠5 := by
  have hs := sourceEq k q r
  have he := endEq k q r
  constructor
  · rw [hs, ←he]
    exact (one_unpadded_strict_first k (tokens0 q r)).1
  · intro t hp ht
    rw [hs]
    exact (one_unpadded_strict_first k (tokens0 q r)).2 t hp ht

#print axioms tokenWord0
#print axioms incTokens0
#print axioms canonical_A_one_first

end BB6.Agent4ACanonicalOneTail
