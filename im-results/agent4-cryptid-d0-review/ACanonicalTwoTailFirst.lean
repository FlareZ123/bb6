import Lean.Elab.Tactic.Omega
import AImplicitCodeFirstReturn
import AOneSource

/-!
# Infinite canonical A family: alternating pairs and 3r+2 terminal ones

All original-source canonical A sections
    L(3k+3, q+1, 3r+2) (k,q,r≥0)
take exactly the mixed A-code primitive time to a pure-unary F/0 section,
and have no intervening F control state.  The proof is literal (full
Turing-machine source) and valid with implicit right blanks.
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

namespace BB6.Agent4ACanonicalTwoTail

open CryptidBoundary
open BB6.BoundaryPadding
open BB6.Agent4AImplicitCode
open BB6.CryptidACodeFirstReturn

def tokens (q r : Nat) : List Bool :=
  List.replicate q false ++ List.replicate (r+1) true

private theorem codeAppend (u v : List Bool) :
    CryptidA.wordCode (u++v) =
      CryptidA.wordCode u ++ CryptidA.wordCode v := by
  induction u with
  | nil => rfl
  | cons b u ih =>
      cases b <;> simp [CryptidA.wordCode,ih,List.append_assoc]

private theorem codeFalse (q : Nat) :
    CryptidA.wordCode (List.replicate q false) = pairs q := by
  induction q with
  | zero => rfl
  | succ q ih =>
      change [true,false] ++ CryptidA.wordCode (List.replicate q false) =
        [true,false] ++ pairs q
      rw [ih]

private theorem codeTrue (r : Nat) :
    CryptidA.wordCode (List.replicate r true) =
      List.replicate (3*r) true := by
  induction r with
  | zero => rfl
  | succ r ih =>
      change [true,true,true] ++ CryptidA.wordCode (List.replicate r true) =
        List.replicate (3*(r+1)) true
      rw [ih]
      have hn : 3*(r+1) = 3+3*r := by omega
      rw [hn]
      simpa using (List.replicate_append_replicate
        (n:=3) (m:=3*r) (a:=true))

private theorem codeTokens (q r : Nat) :
    CryptidA.wordCode (tokens q r) =
      pairs q ++ List.replicate (3*(r+1)) true := by
  unfold tokens
  rw [codeAppend,codeFalse,codeTrue]

private theorem incAppend (u v : List Bool) :
    CryptidA.wordInc (u++v) =
      CryptidA.wordInc u + CryptidA.wordInc v := by
  induction u with
  | nil => simp [CryptidA.wordInc]
  | cons b u ih =>
      cases b <;> simp [CryptidA.wordInc,ih,Nat.add_assoc]

private theorem incFalse (q : Nat) :
    CryptidA.wordInc (List.replicate q false) = q := by
  induction q with
  | zero => rfl
  | succ q ih =>
      change 1+CryptidA.wordInc (List.replicate q false) = q+1
      omega

private theorem incTrue (r : Nat) :
    CryptidA.wordInc (List.replicate r true) = 4*r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      change 4+CryptidA.wordInc (List.replicate r true) = 4*(r+1)
      omega

theorem incTokens (q r : Nat) :
    CryptidA.wordInc (tokens q r) = q+4*(r+1) := by
  simp [tokens,incAppend,incFalse,incTrue]

/-- Canonical physical 01-alternation suffix equals a leading zero
followed by q code-10 tokens, r+1 code-111 tokens; the terminal zero is
the (unwritten) blank tape, not an additional coded symbol. -/
theorem tokenWord (q r : Nat) :
    oppairs (q+1) ++ List.replicate (3*r+2) true =
      false :: CryptidA.wordCode (tokens q r) := by
  have hrep : true :: List.replicate (3*r+2) true =
      List.replicate (3*(r+1)) true := by
    calc
      true :: List.replicate (3*r+2) true =
        List.replicate 1 true ++ List.replicate (3*r+2) true := rfl
      _ = List.replicate (1+(3*r+2)) true :=
        List.replicate_append_replicate
      _ = List.replicate (3*(r+1)) true := by
        congr 1
        omega
  have hfront :
      oppairs (q+1) ++ List.replicate (3*r+2) true =
      false :: (pairs q ++
        (true :: List.replicate (3*r+2) true)) := by
    calc
      _ = (false :: (true :: oppairs q)) ++
        List.replicate (3*r+2) true := rfl
      _ = false :: ((true :: oppairs q) ++
        List.replicate (3*r+2) true) := rfl
      _ = false :: ((pairs q ++ [true]) ++
        List.replicate (3*r+2) true) := by
          rw [BB6.AOneSource.one_oppairs]
      _ = false :: (pairs q ++
        (true :: List.replicate (3*r+2) true)) := by
          simp [List.append_assoc]
  rw [hfront,hrep,codeTokens]

private theorem sourceEq (k q r : Nat) :
    DRegularSource.sourceSection ⟨3*k+3,q+1,3*r+2⟩ =
      implicitStart k (tokens q r) := by
  have hn : (3*k+3)-2 = 3*k+1 := by omega
  simp only [DRegularSource.sourceSection,implicitStart,hn,
    List.append_assoc]
  rw [tokenWord]

private theorem endEq (k q r : Nat) :
    mixedEnd k (tokens q r) [] =
      DRegularSource.sourceSection ⟨8*k+19+2*q+8*r,0,0⟩ := by
  have hn : (8*k+19+2*q+8*r)-2 = 8*k+17+2*q+8*r := by omega
  have hrep :
      List.replicate (8*k+19+2*q+8*r) true =
        true :: true :: List.replicate (8*k+17+2*q+8*r) true := by
    calc
      _ = List.replicate (2+(8*k+17+2*q+8*r)) true := by
        congr 1
        omega
      _ = List.replicate 2 true ++
          List.replicate (8*k+17+2*q+8*r) true :=
          (List.replicate_append_replicate).symm
      _ = _ := rfl
  have htime :
      2*(4*k+3+(q+4*(r+1)))+5 = 8*k+19+2*q+8*r := by omega
  unfold mixedEnd
  simp only [List.append_nil]
  change
    (⟨[],false,List.replicate
      (2*(4*k+3+CryptidA.wordInc (tokens q r))+5) true,5⟩ : Cfg) =
    DRegularSource.sourceSection ⟨8*k+19+2*q+8*r,0,0⟩
  rw [incTokens,htime,hrep]
  simp [DRegularSource.sourceSection,hn,oppairs,init]

/-- One infinite canonical A two-tail family is now a first-control-F
return with precise full-machine step count and unary output.
All q,r,k are arbitrary natural numbers. -/
theorem canonical_A_two_first (k q r : Nat) :
    ObsEq
      (run (codeCost k (tokens q r))
        (DRegularSource.sourceSection ⟨3*k+3,q+1,3*r+2⟩))
      (DRegularSource.sourceSection ⟨8*k+19+2*q+8*r,0,0⟩) ∧
    ∀ t, 0<t → t<codeCost k (tokens q r) →
      (run t (DRegularSource.sourceSection ⟨3*k+3,q+1,3*r+2⟩)).st ≠ 5 := by
  have hs := sourceEq k q r
  have he := endEq k q r
  constructor
  · rw [hs, ←he]
    exact (code_unpadded_strict_first k (tokens q r)).1
  · intro t hp ht
    rw [hs]
    exact (code_unpadded_strict_first k (tokens q r)).2 t hp ht

#print axioms tokenWord
#print axioms incTokens
#print axioms canonical_A_two_first

end BB6.Agent4ACanonicalTwoTail
