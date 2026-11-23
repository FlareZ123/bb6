import Lean.Elab.Tactic.Omega
import ACanonicalOneTailFirst
import AImplicitDoubleTailFirst

/-!
# Original canonical A residue b ≡ 1 (mod 3), physical first return

Every canonical L(3k+3,q+1,3r+1) with k,q,r arbitrary natural
numbers has a first physically blank-left F/0 return at its exact
source-code clock.  The C/1-D/1-F internal F visit is correctly
excluded by the physical predicate, not by the mathematically false
"No control-state F" claim.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

namespace BB6.Agent4ACanonicalDoubleTail

open CryptidBoundary
open BB6.BoundaryPadding
open BB6.Agent4ACanonicalOneTail
open BB6.Agent4AImplicitDouble
open BB6.CryptidA1100CodeFirst
open BB6.CryptidELowCanonicalFirst

/-- Every 1^(3r+2) tail is encoded 111^r, 11, no explicit zero.
The two zeros used by A1100CodeFirst are precisely blank tape cells. -/
theorem tokenWordDouble (q r : Nat) :
    oppairs (q+1) ++ List.replicate (3*r+1) true =
      false :: (CryptidA.wordCode (tokens0 q r) ++ [true,true]) := by
  have hrep :
      true :: List.replicate (3*r+1) true =
        List.replicate (3*r) true ++ [true,true] := by
    calc
      true :: List.replicate (3*r+1) true =
        List.replicate 2 true ++ List.replicate (3*r) true := rfl
      _ = List.replicate (2+3*r) true :=
        List.replicate_append_replicate
      _ = List.replicate (3*r+2) true := by congr 1; omega
      _ = List.replicate (3*r) true ++ List.replicate 2 true :=
        (List.replicate_append_replicate).symm
      _ = List.replicate (3*r) true ++ [true,true] := rfl
  calc
    oppairs (q+1) ++ List.replicate (3*r+1) true =
        false :: ((pairs q ++ [true]) ++
          List.replicate (3*r+1) true) := by
        change (false :: (true :: oppairs q)) ++
            List.replicate (3*r+1) true = _
        rw [BB6.AOneSource.one_oppairs]
        rfl
    _ = false :: (pairs q ++
          (true :: List.replicate (3*r+1) true)) := by
        simp [List.append_assoc]
    _ = false :: (pairs q ++
          (List.replicate (3*r) true ++ [true,true])) := by
        rw [hrep]
    _ = false :: ((pairs q ++ List.replicate (3*r) true) ++
          [true,true]) := by simp [List.append_assoc]
    _ = false :: (CryptidA.wordCode (tokens0 q r) ++
          [true,true]) := by rw [codeTokens0]

private theorem sourceEq (k q r : Nat) :
    DRegularSource.sourceSection ⟨3*k+3,q+1,3*r+1⟩ =
      implicitDouble k (tokens0 q r) := by
  have hn : (3*k+3)-2 = 3*k+1 := by omega
  simp only [DRegularSource.sourceSection,implicitDouble,hn,
    List.append_assoc]
  rw [tokenWordDouble]

private theorem endEq (k q r : Nat) :
    (⟨[],false,
      List.replicate (2*(4*k+3+CryptidA.wordInc (tokens0 q r))+1) true ++
        (false::List.replicate 6 true),5⟩ : Cfg) =
      DRegularSource.sourceSection ⟨8*k+7+2*q+8*r,1,5⟩ := by
  have hn : (8*k+7+2*q+8*r)-2 = 8*k+5+2*q+8*r := by omega
  have hrep :
      List.replicate (8*k+7+2*q+8*r) true =
        true :: true :: List.replicate (8*k+5+2*q+8*r) true := by
    calc
      _ = List.replicate (2+(8*k+5+2*q+8*r)) true := by
        congr 1
        omega
      _ = List.replicate 2 true ++
          List.replicate (8*k+5+2*q+8*r) true :=
          (List.replicate_append_replicate).symm
      _ = _ := rfl
  have ht :
      2*(4*k+3+(q+4*r))+1 = 8*k+7+2*q+8*r := by omega
  rw [incTokens0,ht,hrep]
  simp [DRegularSource.sourceSection,init,hn,oppairs,
    List.append_assoc,List.replicate_append_replicate]

theorem canonical_A_double_first (k q r : Nat) :
    ObsEq
      (run (codeTime k (tokens0 q r))
        (DRegularSource.sourceSection ⟨3*k+3,q+1,3*r+1⟩))
      (DRegularSource.sourceSection ⟨8*k+7+2*q+8*r,1,5⟩) ∧
    ∀ t, 0<t → t<codeTime k (tokens0 q r) →
      ¬BlankLeftF
        (run t (DRegularSource.sourceSection ⟨3*k+3,q+1,3*r+1⟩)) := by
  have hs := sourceEq k q r
  have he := endEq k q r
  constructor
  · rw [hs,←he]
    exact (double_implicit_strict_first k (tokens0 q r)).1
  · intro t hpos ht
    rw [hs]
    exact (double_implicit_strict_first k (tokens0 q r)).2 t hpos ht

#print axioms tokenWordDouble
#print axioms canonical_A_double_first

end BB6.Agent4ACanonicalDoubleTail
