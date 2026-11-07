import Lean.Elab.Tactic.Omega
import ThirdTailPositive
import ThirdTailArithmetic
import ABridgeTwo
import BoundaryPadding

set_option maxHeartbeats 8000000
namespace BB6.Agent2ThirdTailSecondAOne
open CryptidBoundary BB6.Agent2ThirdTailPositive

private theorem wordCode_append (xs ys : List Bool) :
    CryptidA.wordCode (xs ++ ys) =
      CryptidA.wordCode xs ++ CryptidA.wordCode ys := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases b <;> simp [CryptidA.wordCode, ih, List.append_assoc]

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

private theorem special_code (r : Nat) :
    CryptidA.wordCode (BB6.ThirdTailArithmetic.special r) =
      List.replicate (6*r+4) true ++
        (false :: List.replicate 12 true) := by
  unfold BB6.ThirdTailArithmetic.special
  rw [wordCode_append, triples_code, CryptidA.wordCode, triples_code]
  have hmul : 3*(2*r+1)=6*r+3 := by omega
  rw [hmul]
  have h : List.replicate (6*r+3) true ++ [true] =
      List.replicate (6*r+4) true := by
    simpa [show [true] = List.replicate 1 true by rfl] using
      (List.replicate_append_replicate (6*r+3) 1 true)
  calc
    List.replicate (6*r+3) true ++
        (true :: false :: List.replicate 12 true)
      = (List.replicate (6*r+3) true ++ [true]) ++
          (false :: List.replicate 12 true) := by
            simpa using
              (List.append_assoc (List.replicate (6*r+3) true)
                [true] (false :: List.replicate 12 true)).symm
    _ = List.replicate (6*r+4) true ++
          (false :: List.replicate 12 true) := by rw [h]

private theorem inc_eq (ws : List Bool) :
    CryptidA.wordInc ws = BB6.ThirdTailArithmetic.inc ws := by
  induction ws with
  | nil => rfl
  | cons b ws ih =>
    cases b <;> simp [CryptidA.wordInc, BB6.ThirdTailArithmetic.inc, ih] <;> omega

private theorem cost_eq (m : Nat) (ws : List Bool) :
    CryptidA.wordCost m ws = BB6.ThirdTailArithmetic.wc m ws := by
  induction ws generalizing m with
  | nil => rfl
  | cons b ws ih =>
    cases b <;> simp [CryptidA.wordCost, BB6.ThirdTailArithmetic.wc, ih] <;> omega

private theorem a_input_shape (t r : Nat) :
    packetTarget (3*t+2) (3*r+1) =
    init (List.replicate (3*(8*t+6)+1) true ++
      false :: (CryptidA.wordCode (BB6.ThirdTailArithmetic.special r) ++
        [true,true])) := by
  simp only [packetTarget,init]
  apply congrArg (fun xs : List Bool => (⟨[],false,xs,5⟩ : Cfg))
  have hn : 8*(3*t+2)+5 = 2+(3*(8*t+6)+1) := by omega
  have hp : 2*(3*r+1)+2 = 3*(2*r+1)+1 := by omega
  have hmul : 3*(2*r+1)=6*r+3 := by omega
  have hprefix :
      List.replicate (8*(3*t+2)+5) true =
        [true,true] ++ List.replicate (3*(8*t+6)+1) true := by
    rw [hn]
    simpa using
      (List.replicate_append_replicate 2 (3*(8*t+6)+1) true).symm
  rw [hprefix,hp,hmul,special_code]
  simp [List.append_assoc]


/-- The q=3r+1 A branch closes after two physical blank cells are made explicit
    for the original 1100 terminal. The unpadded endpoint is physically equal. -/
theorem a_q1_next (t r : Nat) :
    BB6.BoundaryPadding.ObsEq
      (CryptidBoundary.run
        (48*r*r+384*r*t+638*r+768*t*t+2504*t+2103)
        (packetTarget (3*t+2) (3*r+1)))
      (⟨[],false,
        List.replicate (64*t+97+16*r) true ++
          (false :: List.replicate 6 true),5⟩ : Cfg) := by
  let K : Nat := 8*t+6
  let m : Nat := 4*K+3
  let ws : List Bool := BB6.ThirdTailArithmetic.special r
  let xs : List Bool :=
    List.replicate (3*K+1) true ++
      false :: (CryptidA.wordCode ws ++ [true,true])
  have hs : packetTarget (3*t+2) (3*r+1) = init xs := by
    simpa [xs,K,ws] using a_input_shape t r
  have ht :
      48*r*r+384*r*t+638*r+768*t*t+2504*t+2103 =
        (12*K*K+41*K+32) +
          (CryptidA.wordCost m ws +
            (2*(m+CryptidA.wordInc ws)+16)) := by
    dsimp [K,m,ws]
    rw [cost_eq, inc_eq]
    exact (BB6.ThirdTailArithmetic.a_first_mod_time t r).symm
  rw [hs,ht]
  have hpad := BB6.BoundaryPadding.source_init_pad
    ((12*K*K+41*K+32) +
      (CryptidA.wordCost m ws +
        (2*(m+CryptidA.wordInc ws)+16))) 2 xs
  have hsource := BB6.Agent35.full_A_code_double K ws []
  let target1 : Cfg :=
    ⟨[],false,
      List.replicate (2*(m+CryptidA.wordInc ws)+1) true ++
        (false :: List.replicate 6 true),5⟩
  have hsource' :
      CryptidBoundary.run
        ((12*K*K+41*K+32) +
          (CryptidA.wordCost m ws +
            (2*(m+CryptidA.wordInc ws)+16)))
        (init (xs ++ List.replicate 2 false)) = target1 := by
    simpa [target1,xs,K,m,List.append_assoc] using hsource
  have hlen :
      2*(m+CryptidA.wordInc ws)+1 = 64*t+97+16*r := by
    dsimp [m,K,ws]
    rw [inc_eq, BB6.ThirdTailArithmetic.inc_special]
    omega
  let target2 : Cfg :=
    ⟨[],false,
      List.replicate (64*t+97+16*r) true ++
        (false :: List.replicate 6 true),5⟩
  have htarget : target1 = target2 := by
    apply congrArg (fun n => (⟨[],false,
      List.replicate n true ++ (false :: List.replicate 6 true),5⟩ : Cfg))
    exact hlen
  have hsourceObs :
      BB6.BoundaryPadding.ObsEq
        (CryptidBoundary.run
          ((12*K*K+41*K+32) +
            (CryptidA.wordCost m ws +
              (2*(m+CryptidA.wordInc ws)+16)))
          (init (xs ++ List.replicate 2 false))) target1 := by
    rw [hsource']
    exact BB6.Padding.cfgEq_refl _
  have htargetObs : BB6.BoundaryPadding.ObsEq target1 target2 := by
    rw [htarget]
    exact BB6.Padding.cfgEq_refl _
  simpa [target2, BB6.BoundaryPadding.ObsEq] using
    (BB6.Padding.cfgEq_trans hpad
      (BB6.Padding.cfgEq_trans hsourceObs htargetObs))

#print axioms a_q1_next
end BB6.Agent2ThirdTailSecondAOne
