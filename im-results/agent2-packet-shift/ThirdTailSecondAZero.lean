import Lean.Elab.Tactic.Omega
import ThirdTailPositive
import ABridgeCode

set_option maxHeartbeats 8000000
namespace BB6.Agent2ThirdTailSecondAZero
open CryptidBoundary BB6.Agent2ThirdTailPositive

private theorem triples_code (n : Nat) :
    CryptidA.wordCode (List.replicate n true) =
      List.replicate (3*n) true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ,CryptidA.wordCode]
    rw [ih]
    have h : List.replicate (3*(n+1)) true =
        [true,true,true] ++ List.replicate (3*n) true := by
      rw [show 3*(n+1)=3+3*n by omega,
        ← List.replicate_append_replicate]
      rfl
    rw [h]

private theorem triples_inc (n : Nat) :
    CryptidA.wordInc (List.replicate n true) = 4*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ,CryptidA.wordInc]
    rw [ih]
    omega

private theorem triples_cost (m n : Nat) :
    CryptidA.wordCost m (List.replicate n true) =
      n*(6*m+29)+12*n*n := by
  induction n generalizing m with
  | zero => simp [CryptidA.wordCost]
  | succ n ih =>
    simp only [List.replicate_succ,CryptidA.wordCost]
    rw [ih]
    grind

private theorem a_input_shape (t r : Nat) :
    packetTarget (3*t+2) (3*r+2) =
    init (List.replicate (3*(8*t+6)+1) true ++
      false :: (CryptidA.wordCode (List.replicate (2*r+2) true) ++
        (false :: List.replicate 14 true))) := by
  simp only [packetTarget,init]
  apply congrArg (fun xs : List Bool => (⟨[],false,xs,5⟩ : Cfg))
  rw [triples_code]
  have hn : 8*(3*t+2)+5 = 2+(3*(8*t+6)+1) := by omega
  have hp : 2*(3*r+2)+2 = 3*(2*r+2) := by omega
  rw [hn,hp,← List.replicate_append_replicate]
  simp [List.append_assoc]

/-- A q≡2 mod3 successor closes at a zero, reentering pure unary F/0. -/
theorem a_q2_next (t r : Nat) :
    run (768*t*t+1928*t+1216+(384*t+494)*r+48*r*r)
      (packetTarget (3*t+2) (3*r+2)) =
    (⟨[],false,List.replicate (64*t+89+16*r) true,5⟩ : Cfg) := by
  let K : Nat := 8*t+6
  let m : Nat := 4*K+3
  let n : Nat := 2*r+2
  let ws : List Bool := List.replicate n true
  have hs : packetTarget (3*t+2) (3*r+2) =
      init (List.replicate (3*K+1) true ++
        false::(CryptidA.wordCode ws ++ (false::List.replicate 14 true))) := by
    exact a_input_shape t r
  have ht :
      768*t*t+1928*t+1216+(384*t+494)*r+48*r*r =
      (12*K*K+41*K+32)+
        (CryptidA.wordCost m ws+
          (2*(m+CryptidA.wordInc ws)+6)) := by
    dsimp [K,m,ws,n]
    rw [triples_inc,triples_cost]
    grind
  rw [hs,ht]
  have h := BB6.Agent35.full_A_code K ws (List.replicate 14 true)
  rw [h]
  apply congrArg (fun xs : List Bool => (⟨[],false,xs,5⟩ : Cfg))
  change List.replicate
      (2*(4*(8*t+6)+3+
        CryptidA.wordInc (List.replicate (2*r+2) true))+5) true ++
        List.replicate 14 true =
      List.replicate (64*t+89+16*r) true
  rw [triples_inc]
  rw [List.replicate_append_replicate]
  have hn : 2*(4*(8*t+6)+3+4*(2*r+2))+5+14 =
      64*t+89+16*r := by omega
  rw [hn]

#print axioms a_q2_next
end BB6.Agent2ThirdTailSecondAZero
