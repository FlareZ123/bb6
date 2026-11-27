import TwoSidedAutomata
import Box17AuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent13.Box33D17V23Block19
open BB6Coverage BB6.Agent4Automata
open Box17 (index decode)

namespace M19
def codes : List (Option (Fin 25)) := [some 8,some 24,some 11,some 18,some 1,some 13,some 17,some 7,some 23,some 5,some 4,some 0]
def partialTable : PartialMachine := fun s => (codes.getD (index s).val none).map decode
def cert : Cert := ⟨⟨#[[(false,0)],[(true,0)],[(true,1)],[(true,2)],[(true,3)],[(false,4)],[(true,4)],[(true,6),(true,15)],[(true,7)],[(true,8)],[(false,6),(false,15)],[(false,2)],[(false,1)],[(true,9)],[(true,13)],[(true,14)],[(false,9)]],#[(0,1),(12,2),(11,3),(0,4),(5,6),(0,0),(10,7),(0,8),(0,9),(16,13),(0,0),(0,0),(0,0),(0,14),(0,15),(10,7),(0,0)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(false,2)],[(true,3)],[(true,2)],[(false,4),(false,24)],[(true,6)],[(false,6)],[(true,8)],[(false,9)],[(true,10)],[(true,11)],[(false,12)],[(true,12),(true,22)],[(false,14)],[(false,15)],[(true,16)],[(false,11)],[(true,18)],[(false,19)],[(true,20)],[(false,20)],[(false,10)],[(true,23)]],#[(0,1),(2,0),(3,5),(0,4),(6,0),(0,0),(8,7),(0,0),(0,9),(10,0),(23,11),(18,12),(13,14),(0,0),(15,0),(16,0),(0,17),(0,0),(0,19),(20,0),(22,21),(0,0),(0,14),(0,24),(6,0)]⟩,#[(.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty))) .empty) (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty))) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))))))),(.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .leaf (.branch (.branch .empty .leaf) .empty))))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty)))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty))) (.branch (.branch .empty .leaf) (.branch .empty (.branch (.branch .empty .leaf) .empty))))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))))) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .empty (.branch .empty .leaf))) .empty) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch .empty .leaf) .empty))) .empty) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch .leaf (.branch (.branch .empty .leaf) .empty))))) (.branch (.branch (.branch (.branch .leaf (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) .empty) .empty)),(.branch (.branch .empty .leaf) (.branch .empty (.branch .empty (.branch .empty .leaf)))),(.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty) (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty)) .empty))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty))) .empty)) (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))) .leaf)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))))) (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) .empty))) (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) .empty) .empty)),(.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty)) (.branch .empty (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)))))),.empty]⟩
theorem checked_row_0 : (row cert (0 : Fin 6) false).all
    (fun j => stateStepOK partialTable cert (0 : Fin 6) false (j / cert.right.edges.size) (j % cert.right.edges.size)) = true := by decide
theorem checked_row_1 : (row cert (0 : Fin 6) true).all
    (fun j => stateStepOK partialTable cert (0 : Fin 6) true (j / cert.right.edges.size) (j % cert.right.edges.size)) = true := by decide
theorem checked_row_2 : (row cert (1 : Fin 6) false).all
    (fun j => stateStepOK partialTable cert (1 : Fin 6) false (j / cert.right.edges.size) (j % cert.right.edges.size)) = true := by decide
theorem checked_row_3 : (row cert (1 : Fin 6) true).all
    (fun j => stateStepOK partialTable cert (1 : Fin 6) true (j / cert.right.edges.size) (j % cert.right.edges.size)) = true := by decide
theorem checked_row_4 : (row cert (2 : Fin 6) false).all
    (fun j => stateStepOK partialTable cert (2 : Fin 6) false (j / cert.right.edges.size) (j % cert.right.edges.size)) = true := by decide
theorem checked_row_5 : (row cert (2 : Fin 6) true).all
    (fun j => stateStepOK partialTable cert (2 : Fin 6) true (j / cert.right.edges.size) (j % cert.right.edges.size)) = true := by decide
theorem checked_row_6 : (row cert (3 : Fin 6) false).all
    (fun j => stateStepOK partialTable cert (3 : Fin 6) false (j / cert.right.edges.size) (j % cert.right.edges.size)) = true := by decide
theorem checked_row_7 : (row cert (3 : Fin 6) true).all
    (fun j => stateStepOK partialTable cert (3 : Fin 6) true (j / cert.right.edges.size) (j % cert.right.edges.size)) = true := by decide
theorem checked_row_8 : (row cert (4 : Fin 6) false).all
    (fun j => stateStepOK partialTable cert (4 : Fin 6) false (j / cert.right.edges.size) (j % cert.right.edges.size)) = true := by decide
theorem checked_row_9 : (row cert (4 : Fin 6) true).all
    (fun j => stateStepOK partialTable cert (4 : Fin 6) true (j / cert.right.edges.size) (j % cert.right.edges.size)) = true := by decide
theorem checked_row_10 : (row cert (5 : Fin 6) false).all
    (fun j => stateStepOK partialTable cert (5 : Fin 6) false (j / cert.right.edges.size) (j % cert.right.edges.size)) = true := by decide
theorem checked_row_11 : (row cert (5 : Fin 6) true).all
    (fun j => stateStepOK partialTable cert (5 : Fin 6) true (j / cert.right.edges.size) (j % cert.right.edges.size)) = true := by decide
theorem left_nonempty : decide (0 < cert.left.edges.size) = true := by decide
theorem right_nonempty : decide (0 < cert.right.edges.size) = true := by decide
theorem left_seed : (cert.left.pop 0).contains (false,0) = true := by decide
theorem right_seed : (cert.right.pop 0).contains (false,0) = true := by decide
theorem start_state : stateOK cert 0 false 0 0 = true := by decide
theorem rows_checked :
  (List.finRange 6).all (fun q => BB6.Agent1NGram.bits.all (fun a =>
    (row cert q a).all
      (fun i => stateStepOK partialTable cert q a
        (i / cert.right.edges.size) (i % cert.right.edges.size)))) = true := by
  simp [BB6.Agent1NGram.bits, List.finRange, checked_row_0, checked_row_1, checked_row_2, checked_row_3, checked_row_4, checked_row_5, checked_row_6, checked_row_7, checked_row_8, checked_row_9, checked_row_10, checked_row_11]
theorem checked : check partialTable cert = true := by
  unfold check
  rw [left_nonempty, right_nonempty, left_seed, right_seed, start_state, rows_checked] <;> rfl
theorem compatible_never (m : Machine) (hm : compatible partialTable m) : NeverHalts m :=
  BB6.Agent4Automata.never partialTable cert checked m hm
#print axioms compatible_never
end M19
end BB6.Agent13.Box33D17V23Block19
