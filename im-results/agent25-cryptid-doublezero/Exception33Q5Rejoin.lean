import Lean.Elab.Tactic.Omega
import DRegularSourceShift
import EAllDouble
import CryptidThree
import ABridgeCode
import BoundaryPadding

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent25Exception33Q5

open CryptidBoundary
open BB6.BoundaryPadding BB6.Padding

def sourceStart (u : Nat) : Cfg :=
  DRegularSource.sourceSection ⟨27*u+7,5,1⟩

def eAllTime (u : Nat) : Nat :=
  BB6.Agent32EAll.duration (9*u+1) 4

def eAllOutput (u : Nat) : Cfg :=
  BB6.Agent32EAll.output (9*u+1) 4 []

def eThreeK (u : Nat) : Nat := 24*u+3

def eThreeTime (u : Nat) : Nat :=
  12*(eThreeK u)*(eThreeK u)+49*(eThreeK u)+58

def eThreeInput (u : Nat) : Cfg :=
  init (List.replicate (3*(eThreeK u)+2) true ++
    false :: ([true,true,true] ++
      (List.replicate 7 true ++ (false :: List.replicate 6 true))))

def eThreeOutput (u : Nat) : Cfg :=
  ⟨[],false,
    List.replicate (8*(eThreeK u)+9) true ++
      (packetThree ++
        (List.replicate 7 true ++ (false :: List.replicate 6 true))),5⟩

def aCodeK (u : Nat) : Nat := 64*u+10

def aCodeWord : List Bool := [false,false,true,true,false,true,true]

def aCodeTime (u : Nat) : Nat :=
  12*(aCodeK u)*(aCodeK u)+49*(aCodeK u)+64+
    CryptidA.wordCost (4*(aCodeK u)+3) aCodeWord+
    2*((4*(aCodeK u)+3)+CryptidA.wordInc aCodeWord)+6

def aCodeInput (u : Nat) : Cfg :=
  init (List.replicate (3*(aCodeK u)+1) true ++
    false :: (CryptidA.wordCode aCodeWord ++ [false]))

def aCodeOutput (u : Nat) : Cfg :=
  ⟨[],false,
    List.replicate
      (2*((4*(aCodeK u)+3)+CryptidA.wordInc aCodeWord)+5) true,5⟩

/-- The authentic L(27u+7,5,1) section is exactly the implicit-blank
    EAllDouble source input with k=9u+1 and q=4. -/
theorem eall_source_return (u : Nat) :
    ObsEq (run (eAllTime u) (sourceStart u)) (eAllOutput u) := by
  have hstart :
      sourceStart u = BB6.Agent32EAll.start (9*u+1) 4 [] := by
    simp [sourceStart, BB6.Agent32EAll.start,
      DRegularSource.sourceSection, CryptidBoundary.init,
      CryptidBoundary.oppairs, CryptidBoundary.pairs,
      List.append_assoc]
  rw [hstart]
  change ObsEq
    (run (BB6.Agent32EAll.duration (9*u+1) 4)
      (BB6.Agent32EAll.start (9*u+1) 4 []))
    (BB6.Agent32EAll.output (9*u+1) 4 [])
  exact BB6.Agent32EAll.all_e_double_implicit_blank (9*u+1) 4

/-- EAllDouble's output is the exact full-E-three input at s=8t+3. -/
theorem eall_to_etriple_input (u : Nat) :
    eAllOutput u = eThreeInput u := by
  have hnum : 8*(9*u+1)+5 = 3*(24*u+3)+4 := by omega
  simp [eAllOutput, eThreeInput, eThreeK,
    BB6.Agent32EAll.output, CryptidBoundary.init,
    hnum, List.replicate_succ, List.append_assoc]

/-- The E-three output is the A-code input up to one explicit far-right blank. -/
theorem etriple_to_acode_input (u : Nat) :
    ObsEq (eThreeOutput u) (aCodeInput u) := by
  let xs : List Bool :=
    List.replicate (3*(aCodeK u)+1) true ++
      (false :: CryptidA.wordCode aCodeWord)
  have hprefix : 8*(eThreeK u)+9 = 3*(aCodeK u)+3 := by
    dsimp [eThreeK, aCodeK]
    omega
  have htail :
      packetThree ++
        (List.replicate 7 true ++ (false :: List.replicate 6 true)) =
      false :: CryptidA.wordCode aCodeWord := by
    decide
  have hout : eThreeOutput u = init xs := by
    simp [eThreeOutput, xs, CryptidBoundary.init,
      hprefix, htail, List.replicate_succ,
      Nat.add_assoc, List.append_assoc]
  have hpad : ObsEq (init xs) (init (xs ++ [false])) := by
    simpa [CryptidBoundary.run] using
      (BB6.BoundaryPadding.source_init_pad 0 1 xs)
  have hinput : init (xs ++ [false]) = aCodeInput u := by
    simp [aCodeInput, xs, aCodeK, List.append_assoc]
  simpa [hout, hinput] using hpad

/-- The A-code word has increment 19, giving the exact unary endpoint. -/
theorem acode_unary_endpoint (u : Nat) :
    aCodeOutput u =
      DRegularSource.sourceSection ⟨512*u+129,0,0⟩ := by
  have hlen :
      2*((4*(aCodeK u)+3)+CryptidA.wordInc aCodeWord)+5 =
        512*u+129 := by
    simp [aCodeK, aCodeWord, CryptidA.wordInc]
    omega
  unfold aCodeOutput
  rw [hlen]
  simp [DRegularSource.sourceSection,
    CryptidBoundary.init, CryptidBoundary.oppairs]

/-- Full original-source exception-33 q=5 continuation for t=3u:
    EAllDouble(q=4) -> E-three -> A-code -> pure unary. -/
theorem exception33_q5_rejoin (u : Nat) :
    ObsEq
      (run (eAllTime u + eThreeTime u + aCodeTime u) (sourceStart u))
      (DRegularSource.sourceSection ⟨512*u+129,0,0⟩) := by
  have h1 := eall_source_return u
  have hEallInput : ObsEq (eAllOutput u) (eThreeInput u) := by
    rw [eall_to_etriple_input u]
    exact BB6.Padding.cfgEq_refl _
  have htransport2 := BB6.BoundaryPadding.source_congr
    (eThreeTime u) hEallInput
  have hraw2 :
      run (eThreeTime u) (eThreeInput u) = eThreeOutput u := by
    simpa [eThreeTime, eThreeInput, eThreeOutput, eThreeK] using
      (CryptidBoundary.full_E_three (eThreeK u)
        (List.replicate 7 true ++ (false :: List.replicate 6 true)))
  have h2 :
      ObsEq (run (eThreeTime u) (eAllOutput u)) (eThreeOutput u) := by
    rw [hraw2] at htransport2
    exact htransport2
  have htransport3 := BB6.BoundaryPadding.source_congr
    (aCodeTime u) (etriple_to_acode_input u)
  have hraw3 :
      run (aCodeTime u) (aCodeInput u) = aCodeOutput u := by
    simpa [aCodeTime, aCodeInput, aCodeOutput] using
      (BB6.Agent35.full_A_code (aCodeK u) aCodeWord [])
  have h3 :
      ObsEq (run (aCodeTime u) (eThreeOutput u)) (aCodeOutput u) := by
    rw [hraw3] at htransport3
    exact htransport3
  have h12 := BB6.BoundaryPadding.source_chain
    (eAllTime u) (eThreeTime u) (sourceStart u)
    (eAllOutput u) (eThreeOutput u) h1 h2
  have h123 := BB6.BoundaryPadding.source_chain
    (eAllTime u + eThreeTime u) (aCodeTime u) (sourceStart u)
    (eThreeOutput u) (aCodeOutput u) h12 h3
  rw [acode_unary_endpoint u] at h123
  simpa [Nat.add_assoc] using h123

#print axioms eall_source_return
#print axioms eall_to_etriple_input
#print axioms etriple_to_acode_input
#print axioms acode_unary_endpoint
#print axioms exception33_q5_rejoin

end BB6.Agent25Exception33Q5
