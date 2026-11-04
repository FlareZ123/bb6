import Lean.Elab.Tactic.Omega
import BlankSixthExceptional
import ESecondSource
import PacketSource
import A110111CodeFirst

set_option maxHeartbeats 100000000
set_option maxRecDepth 55000

namespace BB6.Agent35SixthRoot
open CryptidBoundary BB6.BoundaryPadding BB6.Padding

private def t (w : Nat) := 27*w+23
private def kB (w : Nat) := 576*w+501
private def kE (w : Nat) := 1536*w+1338
private def kA (w : Nat) := 4096*w+3570
private def ys : List Bool := false :: List.replicate 6 true
private def ws : List Bool := [false,false,false]
private def zs : List Bool := [true,true,true]
private def costB (w : Nat) := 12*(kB w)*(kB w)+49*(kB w)+40
private def costE (w : Nat) := 12*(kE w)*(kE w)+49*(kE w)+58+6
private def costA (w : Nat) :=
  (12*(kA w)*(kA w)+41*(kA w)+32) +
  (CryptidA.wordCost (4*(kA w)+3) ws +
    (2*(4*(kA w)+3+CryptidA.wordInc ws)+24))
private def costAll (w : Nat) :=
  BB6.Agent31SecondSource.secondCost (t w) +
  (costB w + (costE w + costA w))

private theorem finish_is_B (w : Nat) :
    BB6.Agent31SecondSource.finish (t w) 1 =
      BB6.Agent31PacketSource.packet (3*(kB w)+2) 2 5 ys := by
  have hn : 8*(8*(t w)+3)+9 = 3*(kB w)+2 := by
    simp only [t,kB]
    omega
  unfold BB6.Agent31SecondSource.finish
  simp only [BB6.Agent31PacketSource.packet,BB6.Agent31PacketSource.word]
  rw [hn]
  rfl

private theorem B_to_E (w : Nat) :
    run (costB w)
      (BB6.Agent31PacketSource.packet (3*(kB w)+2) 2 5 ys) =
    BB6.Agent31PacketSource.packet (3*(kE w)+4) 1 5 ys := by
  have hn : 8*(kB w)+10 = 3*(kE w)+4 := by
    simp only [kB,kE]
    omega
  unfold costB
  rw [BB6.Agent31PacketSource.b_packet (kB w) 1 5 ys]
  rw [hn]

private theorem E_to_A (w : Nat) :
    run (costE w)
      (BB6.Agent31PacketSource.packet (3*(kE w)+4) 1 5 ys) =
    BB6.Agent31PacketSource.packet (3*(kA w)+3) 3 2 ys := by
  have hn : 8*(kE w)+9 = 3*(kA w)+3 := by
    simp only [kE,kA]
    omega
  unfold costE
  rw [BB6.Agent31PacketSource.e_packet (kE w) 1 2 ys]
  rw [hn]

private theorem A_start (w : Nat) :
    BB6.Agent31PacketSource.packet (3*(kA w)+3) 3 2 ys =
    init (List.replicate (3*(kA w)+1) true ++
      false :: (CryptidA.wordCode ws ++
        BB6.CryptidA110111CodeFirst.packet zs)) := by
  have hn : List.replicate (3*(kA w)+3) true =
      true :: true :: List.replicate (3*(kA w)+1) true := by
    calc
      _ = List.replicate (2+(3*(kA w)+1)) true := by
        congr 1
        omega
      _ = List.replicate 2 true ++
          List.replicate (3*(kA w)+1) true :=
          (List.replicate_append_replicate).symm
      _ = _ := rfl
  have hword : BB6.Agent31PacketSource.word 3 2 ys =
    false :: (CryptidA.wordCode ws ++
      BB6.CryptidA110111CodeFirst.packet zs) := by decide
  unfold BB6.Agent31PacketSource.packet
  rw [hn,hword]
  simp [init,List.append_assoc]

private theorem A_output (w : Nat) :
    (⟨[],false,
      List.replicate
        (2*(4*(kA w)+3+CryptidA.wordInc ws)+5) true ++
      BB6.CryptidA110111CodeFirst.tail zs,5⟩ : Cfg) =
    DRegularSource.sourceSection ⟨8*(kA w)+17,3,2⟩ := by
  have hi : CryptidA.wordInc ws = 3 := by decide
  have ht : BB6.CryptidA110111CodeFirst.tail zs =
      oppairs 3 ++ List.replicate 2 true := by decide
  have hn : 2*(4*(kA w)+3+3)+5 = 8*(kA w)+17 := by omega
  have hr : List.replicate (8*(kA w)+17) true =
      true :: true :: List.replicate (8*(kA w)+15) true := by
    have hx : 8*(kA w)+17 = 2+(8*(kA w)+15) := by omega
    calc
      _ = List.replicate (2+(8*(kA w)+15)) true :=
        congrArg (fun n : Nat => List.replicate n true) hx
      _ = List.replicate 2 true ++
          List.replicate (8*(kA w)+15) true :=
          (List.replicate_append_replicate).symm
      _ = _ := rfl
  rw [hi,hn,ht,hr]
  simp [DRegularSource.sourceSection,init,oppairs,
    show (8*(kA w)+17)-2=8*(kA w)+15 by omega,
    List.append_assoc]

private theorem A_to_regular (w : Nat) :
    run (costA w)
      (BB6.Agent31PacketSource.packet (3*(kA w)+3) 3 2 ys) =
    DRegularSource.sourceSection ⟨8*(kA w)+17,3,2⟩ := by
  rw [A_start]
  have h := (BB6.CryptidA110111CodeFirst.full_A_code_110111_first_return
     (kA w) ws zs).1
  have hc : costA w =
    (12*(kA w)*(kA w)+41*(kA w)+32) +
      (CryptidA.wordCost (4*(kA w)+3) ws +
        (2*(4*(kA w)+3+CryptidA.wordInc ws)+24)) := rfl
  rw [hc,h]
  exact A_output w

/-- Four exact source-transported designated returns past the first exceptional
    E endpoint, for every t = 27w+23. The output is again a regular L-section. -/
theorem universal_reentry (w : Nat) :
    ObsEq
      (run (costAll w) (BB6.Agent32EAll.output (3*(t w)+1) 3 []))
      (DRegularSource.sourceSection ⟨8*(kA w)+17,3,2⟩) := by
  have hmiddle :
      BB6.Agent32EAll.output (3*(t w)+1) 3 [] =
        BB6.Agent31SecondSource.middle (t w) 1 := by
    rfl
  unfold costAll
  rw [run_add,hmiddle,BB6.Agent31SecondSource.second_source,
    finish_is_B,run_add,B_to_E,run_add,E_to_A,A_to_regular]
  exact cfgEq_refl _

/-- The authentic blank orbit's sixth E exception is in the universally
    rejoining residue class. This is exact finite model computation. -/
theorem true_root_t_mod27 :
    BB6.Agent25SixthRoot.t6 % 27 = 23 := by decide

/-- The genuinely blank six-state machine returns to the regular
    L(a,3,2) section after four further source-certified macro endpoints. -/
theorem blank_sixth_reentry :
    let w := BB6.Agent25SixthRoot.t6 / 27
    ObsEq
      (run
        (BB6.Agent25SixthRoot.nextRawTime + costAll w)
        blank)
      (DRegularSource.sourceSection ⟨8*(kA w)+17,3,2⟩) := by
  dsimp
  let w := BB6.Agent25SixthRoot.t6 / 27
  have ht : BB6.Agent25SixthRoot.t6 = t w := by
    have hmod := true_root_t_mod27
    dsimp [t,w]
    omega
  have hs := universal_reentry w
  rw [←ht] at hs
  exact source_chain
    BB6.Agent25SixthRoot.nextRawTime (costAll w)
    blank (BB6.Agent32EAll.output
      (3*BB6.Agent25SixthRoot.t6+1) 3 [])
    (DRegularSource.sourceSection ⟨8*(kA w)+17,3,2⟩)
    BB6.Agent25SixthRoot.first_nonregular_original hs

#print axioms universal_reentry
#print axioms true_root_t_mod27
#print axioms blank_sixth_reentry

end BB6.Agent35SixthRoot
