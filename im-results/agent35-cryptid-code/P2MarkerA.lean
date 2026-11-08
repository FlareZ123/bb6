import Lean.Elab.Tactic.Omega
import PacketP2ResetSource
import A1101010111Code
import CodeImplicitNil
import P2K4Shapes

namespace BB6.Agent35MarkerA
open CryptidBoundary BB6.Agent31PacketSource
open BB6.Agent35K4Shapes (marker)
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

def code (q r : Nat) := List.replicate q false ++ List.replicate r true
def tailCode (q r : Nat) := code q r ++ [false,false,false,true]

theorem code_append (xs ys : List Bool) :
    CryptidA.wordCode (xs ++ ys) = CryptidA.wordCode xs ++ CryptidA.wordCode ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [CryptidA.wordCode, ih]

theorem pair_code (q : Nat) :
    CryptidA.wordCode (List.replicate q false) = pairs q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    change [true,false] ++ CryptidA.wordCode (List.replicate q false) = _
    rw [ih]
    rfl

theorem triple_code (r : Nat) :
    CryptidA.wordCode (List.replicate r true) = List.replicate (3*r) true := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change [true,true,true] ++ CryptidA.wordCode (List.replicate r true) = _
    rw [ih,show 3*(r+1)=3+3*r by omega]
    rw [←List.replicate_append_replicate]
    rfl

theorem code_word (q r : Nat) :
    CryptidA.wordCode (code q r) = pairs q ++ List.replicate (3*r) true := by
  rw [code,code_append,pair_code,triple_code]

private theorem oppairs_false (q : Nat) :
    oppairs q ++ [false] = false :: pairs q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simpa [oppairs,pairs,List.append_assoc] using
      congrArg (fun xs : List Bool => false :: true :: xs) ih

private theorem prepare (ka q p : Nat) :
    packet (3*ka+3) q p marker =
      init (List.replicate (3*ka+1) true ++
        false :: (pairs q ++ (List.replicate p true ++ marker))) := by
  have hn : 3*ka+3 = 2+(3*ka+1) := by omega
  have hw :
      oppairs q ++ (false :: (List.replicate p true ++ marker)) =
        false :: (pairs q ++ (List.replicate p true ++ marker)) := by
    calc
      _ = (oppairs q ++ [false]) ++ (List.replicate p true ++ marker) := by
        simp [List.append_assoc]
      _ = _ := by rw [oppairs_false]; simp [List.append_assoc]
  simp only [packet,word,init]
  rw [hn, ←List.replicate_append_replicate,hw]
  rfl

theorem tail0 (q r : Nat) :
    pairs q ++ (List.replicate (3*r) true ++ marker) =
      CryptidA.wordCode (code q r) ++
        (false :: [true,false,true,false,true,true,true]) := by
  rw [code_word]
  simp [marker,List.append_assoc]

theorem tail1 (q r : Nat) :
    pairs q ++ (List.replicate (3*r+1) true ++ marker) =
      CryptidA.wordCode (tailCode q r) := by
  rw [tailCode,code_append,code_word]
  rw [←List.replicate_append_replicate]
  simp [marker,CryptidA.wordCode,List.append_assoc]

theorem tail2 (q r : Nat) :
    pairs q ++ (List.replicate (3*r+2) true ++ marker) =
      CryptidA.wordCode (code q r) ++
        [true,true,false,true,false,true,false,true,true,true] := by
  rw [code_word, ←List.replicate_append_replicate]
  simp [marker,List.append_assoc]

theorem shape_zero (ka q r : Nat) :
    packet (3*ka+3) q (3*r) marker =
      init (List.replicate (3*ka+1) true ++ false ::
        (CryptidA.wordCode (code q r) ++
          (false :: [true,false,true,false,true,true,true]))) := by
  rw [prepare,tail0]

theorem shape_one (ka q r : Nat) :
    packet (3*ka+3) q (3*r+1) marker =
      init (List.replicate (3*ka+1) true ++ false ::
         CryptidA.wordCode (tailCode q r)) := by
  rw [prepare,tail1]

theorem shape_two (ka q r : Nat) :
    packet (3*ka+3) q (3*r+2) marker =
      init (List.replicate (3*ka+1) true ++ false ::
        (CryptidA.wordCode (code q r) ++
          [true,true,false,true,false,true,false,true,true,true])) := by
  rw [prepare,tail2]

def aTime0 (ka q r : Nat) :=
  (12*ka*ka+41*ka+32)+
    (CryptidA.wordCost (4*ka+3) (code q r) +
      (2*((4*ka+3)+CryptidA.wordInc (code q r))+6))
def aTime1 (ka q r : Nat) :=
  (12*ka*ka+41*ka+32)+
    (CryptidA.wordCost (4*ka+3) (tailCode q r) +
      (2*((4*ka+3)+CryptidA.wordInc (tailCode q r))+6))
def aTime2 (ka q r : Nat) :=
  (12*ka*ka+41*ka+32)+
    (CryptidA.wordCost (4*ka+3) (code q r) +
      (2*((4*ka+3)+CryptidA.wordInc (code q r))+36))

theorem close_zero (ka q r : Nat) :
    run (aTime0 ka q r) (packet (3*ka+3) q (3*r) marker) =
      (⟨[],false,List.replicate
        (2*((4*ka+3)+CryptidA.wordInc (code q r))+5) true ++
          [true,false,true,false,true,true,true],5⟩ : Cfg) := by
  rw [shape_zero]
  exact BB6.Agent35.full_A_code ka (code q r)
    [true,false,true,false,true,true,true]

theorem close_one (ka q r : Nat) :
    run (aTime1 ka q r) (packet (3*ka+3) q (3*r+1) marker) =
      (⟨[],false,List.replicate
        (2*((4*ka+3)+CryptidA.wordInc (tailCode q r))+5) true,5⟩ : Cfg) := by
  rw [shape_one]
  exact BB6.Agent32Code.full_A_code_implicit_nil ka (tailCode q r)

theorem close_two (ka q r : Nat) :
    run (aTime2 ka q r) (packet (3*ka+3) q (3*r+2) marker) =
      (⟨[],false,List.replicate
        (2*((4*ka+3)+CryptidA.wordInc (code q r))+5) true ++
          [false,true,false,true,false,true,false,true,false],5⟩ : Cfg) := by
  rw [shape_two]
  exact BB6.Agent26ACode.full_A_code_1101010111 ka (code q r) []

/-- Uniform source certificate for every A-index packet with the changed
01010111 marker, unrestricted in both q and p. -/
theorem all_A_marker_returns (ka q p : Nat) :
    ∃ (T n : Nat),
       run T (packet (3*ka+3) q p marker) =
           (⟨[],false,List.replicate n true ++
             [true,false,true,false,true,true,true],5⟩ : Cfg) ∨
       run T (packet (3*ka+3) q p marker) =
           (⟨[],false,List.replicate n true,5⟩ : Cfg) ∨
       run T (packet (3*ka+3) q p marker) =
           (⟨[],false,List.replicate n true ++
             [false,true,false,true,false,true,false,true,false],5⟩ : Cfg) := by
  let r := p / 3
  have hcases : p=3*r ∨ p=3*r+1 ∨ p=3*r+2 := by
    have hm := Nat.mod_add_div p 3
    dsimp [r]
    omega
  rcases hcases with h0 | h1 | h2
  · refine ⟨aTime0 ka q r,
      2*((4*ka+3)+CryptidA.wordInc (code q r))+5,Or.inl ?_⟩
    rw [h0]
    exact close_zero ka q r
  · refine ⟨aTime1 ka q r,
      2*((4*ka+3)+CryptidA.wordInc (tailCode q r))+5,Or.inr (Or.inl ?_)⟩
    rw [h1]
    exact close_one ka q r
  · refine ⟨aTime2 ka q r,
      2*((4*ka+3)+CryptidA.wordInc (code q r))+5,Or.inr (Or.inr ?_)⟩
    rw [h2]
    exact close_two ka q r

#print axioms all_A_marker_returns
#print axioms close_zero
#print axioms close_one
#print axioms close_two
end BB6.Agent35MarkerA
