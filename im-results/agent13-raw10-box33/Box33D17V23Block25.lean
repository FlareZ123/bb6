import TwoSidedAutomata
import Box17AuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent13.Box33D17V23Block25
open BB6Coverage BB6.Agent4Automata
open Box17 (index decode)

namespace M25
def codes : List (Option (Fin 25)) := [some 8,some 22,some 11,some 2,some 1,some 13,some 17,some 9,some 23,some 5,some 2,some 0]
def partialTable : PartialMachine := fun s => (codes.getD (index s).val none).map decode
def cert : Cert := ⟨⟨#[[(false,0)],[(true,0)],[(false,1),(false,10)],[(true,2)],[(false,2)],[(false,4)],[(true,5)],[(false,6)],[(false,7)],[(false,8)],[(true,9)],[(true,6)]],#[(0,1),(2,0),(4,3),(0,0),(5,0),(0,6),(7,11),(8,0),(9,0),(0,10),(2,0),(0,0)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(false,2)],[(true,3)],[(false,3),(false,18)],[(true,5)],[(false,6)],[(true,6)],[(false,8)],[(false,9)],[(true,10)],[(true,1),(true,11)],[(false,12)],[(false,13)],[(true,14)],[(false,10)],[(false,11)],[(false,17)]],#[(0,1),(2,12),(3,0),(5,4),(0,0),(0,6),(7,8),(0,0),(9,0),(10,0),(16,11),(17,12),(13,0),(14,0),(0,15),(0,0),(0,0),(18,0),(5,0)]⟩,#[(.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) .leaf) (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty))) (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty))) (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty) (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty)) .leaf))),(.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)) (.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))))),(.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))))) (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) (.branch .leaf (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf))) .empty) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty)) (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty .leaf))) .empty) .empty))),(.branch (.branch .empty (.branch .empty (.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) .empty))) (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty)) (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .leaf (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty)) (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty))))),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch .empty .leaf) .empty)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))) .leaf)),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .leaf) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch (.branch .empty .leaf) .empty))))) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .leaf (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty))) (.branch (.branch .empty .leaf) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))),.empty]⟩
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
end M25
end BB6.Agent13.Box33D17V23Block25
