import Lean.Elab.Tactic.Omega
import ThirdTailPositive
import ThirdTailArithmetic
import ABridgeCode
import A110TriplePairs

set_option maxHeartbeats 8000000
namespace BB6.Agent2ThirdTailSecondAThree
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
    packetTarget (3*t+2) (3*r+3) =
    init (List.replicate (3*(8*t+6)+1) true ++
      false :: (CryptidA.wordCode (List.replicate (2*r+2) true) ++
        ([true,true,false] ++
          (CryptidBoundary.pairs 0 ++
            ([true,true,true] ++ List.replicate 11 true))))) := by
  simp only [packetTarget,init]
  apply congrArg (fun xs : List Bool => (⟨[],false,xs,5⟩ : Cfg))
  rw [triples_code]
  have hn : 8*(3*t+2)+5 = 2+(3*(8*t+6)+1) := by omega
  have hp : 2*(3*r+3)+2 = 3*(2*r+2)+2 := by omega
  have hmul : 3*(2*r+2)=6*r+6 := by omega
  have hprefix :
      List.replicate (8*(3*t+2)+5) true =
        [true,true] ++ List.replicate (3*(8*t+6)+1) true := by
    rw [hn]
    simpa using
      (List.replicate_append_replicate 2 (3*(8*t+6)+1) true).symm
  rw [hprefix,hp,hmul]
  simp [triples_code,CryptidBoundary.pairs,List.append_assoc] <;> omega

/-- The q=3r+3 A branch passes through the original 110111 A-to-E portal
    and returns to a packet with two 01 pairs and eleven trailing ones. -/
theorem a_q3_next (t r : Nat) :
    CryptidBoundary.run
      (48*r*r+384*r*t+494*r+768*t*t+1928*t+1234)
      (packetTarget (3*t+2) (3*r+3)) =
    (⟨[],false,
      List.replicate (64*t+75+16*r) true ++
        (CryptidBoundary.oppairs 2 ++
          (false :: List.replicate 11 true)),5⟩ : Cfg) := by
  let K : Nat := 8*t+6
  let m : Nat := 4*K+3
  let ws : List Bool := List.replicate (2*r+2) true
  let ys : List Bool := List.replicate 11 true
  have hs : packetTarget (3*t+2) (3*r+3) =
      init (List.replicate (3*K+1) true ++
        false :: (CryptidA.wordCode ws ++
          ([true,true,false] ++
            (CryptidBoundary.pairs 0 ++ ([true,true,true] ++ ys))))) := by
    simpa [K,m,ws,ys] using a_input_shape t r
  have hinc : CryptidA.wordInc ws =
      BB6.ThirdTailArithmetic.inc ws := by
    dsimp [ws]
    rw [triples_inc, BB6.ThirdTailArithmetic.inc_triples]
  have hcost : CryptidA.wordCost m ws =
      BB6.ThirdTailArithmetic.wc m ws := by
    dsimp [ws]
    rw [triples_cost, BB6.ThirdTailArithmetic.wc_triples]
  have ht :
      48*r*r+384*r*t+494*r+768*t*t+1928*t+1234 =
        (12*K*K+41*K+32) +
          (CryptidA.wordCost m ws +
            (2*(m+CryptidA.wordInc ws)+24)) := by
    dsimp [K,m,ws]
    rw [hcost,hinc]
    exact (BB6.ThirdTailArithmetic.a_third_mod_time t r).symm
  rw [hs,ht]
  rw [CryptidBoundary.run_add, CryptidBoundary.prefix_A]
  change CryptidBoundary.run
    (CryptidA.wordCost m ws +
      (2*(m+CryptidA.wordInc ws)+24))
    (BB6.Agent35.aBoundary m
      (CryptidA.wordCode ws ++
        ([true,true,false] ++
          (CryptidBoundary.pairs 0 ++ ([true,true,true] ++ ys))))) = _
  rw [CryptidBoundary.run_add, BB6.Agent35.a_code_return]
  change CryptidBoundary.run
    (2*(m+CryptidA.wordInc ws)+24)
    (CryptidBoundary.preA (m+CryptidA.wordInc ws)
      ([true,true,false] ++
        (CryptidBoundary.pairs 0 ++ ([true,true,true] ++ ys)))) = _
  have h := BB6.CryptidBridge.a_110_triple_pairs_return
    (m+CryptidA.wordInc ws) 0 ys
  have hlen :
      2*(m+CryptidA.wordInc ws)+5 = 64*t+75+16*r := by
    dsimp [m,K,ws]
    rw [triples_inc]
    omega
  simpa [ys,hlen] using h

#print axioms a_q3_next
end BB6.Agent2ThirdTailSecondAThree
