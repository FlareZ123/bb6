import TwoSidedAutomata
import Box17AuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent13.Box33D17V24PairBlocks
open BB6Coverage BB6.Agent4Automata
open Box17 (index decode)

namespace M0
def codes : List (Option (Fin 25)) := [some 8,some 3,some 11,some 2,some 1,some 13,some 17,some 0,some 24,some 17,some 24,some 12]
def partialTable : PartialMachine := fun s => (codes.getD (index s).val none).map decode
def cert : Cert := ⟨⟨#[[(false,0)],[(true,0)],[(true,1)],[(true,2),(true,3)],[(false,1)],[(false,2)],[(false,3)],[(true,6)]],#[(0,1),(4,2),(5,3),(6,3),(0,0),(0,0),(0,7),(0,0)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(false,2)],[(true,1)],[(true,4),(true,5)],[(false,3),(false,6)]],#[(0,1),(2,4),(3,0),(6,0),(0,5),(0,5),(6,0)]⟩,#[(.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .leaf) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch .empty .leaf) (.branch (.branch .leaf .leaf) .empty)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))))),(.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch .empty .leaf))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)))),(.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)),(.branch .empty (.branch .leaf (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty))),(.branch (.branch .empty .leaf) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))),.empty,(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)) (.branch .empty .leaf)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) .empty))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)))),(.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty))]⟩
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
end M0

namespace M1
def codes : List (Option (Fin 25)) := [some 8,some 3,some 11,some 2,some 1,some 13,some 17,some 13,some 24,some 0,some 24,some 10]
def partialTable : PartialMachine := fun s => (codes.getD (index s).val none).map decode
def cert : Cert := ⟨⟨#[[(false,0)],[(true,0)],[(true,1)],[(true,2),(true,3)],[(false,3)]],#[(0,1),(0,2),(0,3),(4,3),(0,0)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(false,2)],[(false,3),(false,4)]],#[(0,1),(2,0),(3,0),(4,0),(4,0)]⟩,#[(.branch .leaf (.branch .empty (.branch .empty (.branch .empty .leaf)))),.empty,(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf)))),.empty,(.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .leaf (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .leaf) .empty),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),.empty,(.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) .leaf))),(.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))]⟩
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
end M1

namespace M2
def codes : List (Option (Fin 25)) := [some 8,some 3,some 11,some 2,some 1,some 13,some 17,some 13,some 24,some 0,some 24,some 8]
def partialTable : PartialMachine := fun s => (codes.getD (index s).val none).map decode
def cert : Cert := ⟨⟨#[[(false,0)],[(true,0)],[(true,1)],[(true,2),(true,3)]],#[(0,1),(0,2),(0,3),(0,3)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(false,2)],[(false,3),(false,4)]],#[(0,1),(2,0),(3,0),(4,0),(4,0)]⟩,#[.leaf,.empty,(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf)))),.empty,.empty,(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .leaf (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .leaf) .empty),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),.empty,(.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) .leaf))),(.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))]⟩
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
end M2

namespace M3
def codes : List (Option (Fin 25)) := [some 8,some 3,some 11,some 2,some 1,some 13,some 17,some 13,some 24,some 0,some 24,some 4]
def partialTable : PartialMachine := fun s => (codes.getD (index s).val none).map decode
def cert : Cert := ⟨⟨#[[(false,0)],[(true,0)],[(true,1)],[(true,2),(true,3)]],#[(0,1),(0,2),(0,3),(0,3)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(false,2)],[(false,3),(false,4)]],#[(0,1),(2,0),(3,0),(4,0),(4,0)]⟩,#[(.branch .leaf (.branch .empty (.branch .empty (.branch .empty .leaf)))),.empty,(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf)))),.empty,.empty,(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .leaf (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .leaf) .empty),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),.empty,(.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) .leaf))),(.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))]⟩
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
end M3

namespace M4
def codes : List (Option (Fin 25)) := [some 8,some 3,some 11,some 2,some 1,some 13,some 17,some 9,some 24,some 0,some 24,some 4]
def partialTable : PartialMachine := fun s => (codes.getD (index s).val none).map decode
def cert : Cert := ⟨⟨#[[(false,0)],[(true,0)],[(true,1),(true,3)],[(true,2)]],#[(0,1),(0,2),(0,3),(0,2)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(false,2)]],#[(0,1),(2,0),(3,0),(2,0)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty),.empty,(.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty),.empty,.empty,(.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)]⟩
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
end M4

namespace M5
def codes : List (Option (Fin 25)) := [some 8,some 3,some 11,some 2,some 1,some 13,some 17,some 0,some 24,some 13,some 23,some 6]
def partialTable : PartialMachine := fun s => (codes.getD (index s).val none).map decode
def cert : Cert := ⟨⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,2)]],#[(0,1),(2,0),(0,3),(2,0)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3),(false,4)],[(false,2)],[(true,2)]],#[(0,1),(2,0),(3,4),(2,0),(2,0)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) .empty))),.empty,(.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch .empty (.branch .leaf .leaf)))),(.branch (.branch .empty .leaf) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch .empty (.branch .leaf .leaf)))),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf))) (.branch .leaf (.branch (.branch .empty .leaf) .empty))),(.branch (.branch .empty .leaf) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty .leaf))),.empty,(.branch .empty (.branch .empty .leaf)),(.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .leaf)),(.branch .empty (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty)]⟩
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
end M5

namespace M6
def codes : List (Option (Fin 25)) := [some 8,some 3,some 11,some 2,some 1,some 13,some 17,some 0,some 24,some 13,some 22,some 19]
def partialTable : PartialMachine := fun s => (codes.getD (index s).val none).map decode
def cert : Cert := ⟨⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(false,2),(true,2)]],#[(0,1),(2,0),(3,3),(2,0)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(false,2)]],#[(0,1),(2,0),(3,0),(2,0)]⟩,#[.leaf,.empty,(.branch (.branch (.branch .empty .leaf) .empty) .empty),.empty,.empty,(.branch .empty .leaf),(.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) .empty),.empty,(.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)]⟩
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
end M6

namespace M7
def codes : List (Option (Fin 25)) := [some 8,some 3,some 11,some 2,some 1,some 13,some 17,some 0,some 24,some 13,some 22,some 1]
def partialTable : PartialMachine := fun s => (codes.getD (index s).val none).map decode
def cert : Cert := ⟨⟨#[[(false,0)],[(true,0),(true,2)],[(false,1),(false,3)],[(false,2)]],#[(0,1),(2,0),(3,1),(2,0)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(false,2)]],#[(0,1),(2,0),(3,0),(2,0)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty),.empty,(.branch (.branch (.branch .empty .leaf) .empty) .empty),.empty,.empty,(.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)),(.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) .empty),.empty,(.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))),(.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)]⟩
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
end M7

namespace M8
def codes : List (Option (Fin 25)) := [some 8,some 3,some 11,some 2,some 1,some 13,some 17,some 13,some 24,some 0,some 20,some 15]
def partialTable : PartialMachine := fun s => (codes.getD (index s).val none).map decode
def cert : Cert := ⟨⟨#[[(false,0)],[(true,0)],[(true,1),(true,3)],[(true,2)]],#[(0,1),(0,2),(0,3),(0,2)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(false,2)]],#[(0,1),(2,0),(3,0),(2,0)]⟩,#[.leaf,.empty,(.branch (.branch (.branch .empty .leaf) .empty) .empty),.empty,.empty,(.branch .empty .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),.empty,(.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)]⟩
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
end M8

namespace M9
def codes : List (Option (Fin 25)) := [some 8,some 3,some 11,some 2,some 1,some 13,some 17,some 0,some 24,some 17,some 20,some 12]
def partialTable : PartialMachine := fun s => (codes.getD (index s).val none).map decode
def cert : Cert := ⟨⟨#[[(false,0)],[(true,0)],[(true,1)],[(true,2),(true,3)],[(false,1)],[(false,2)],[(false,3)],[(true,6)]],#[(0,1),(4,2),(5,3),(6,3),(0,0),(0,0),(0,7),(0,0)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(false,2)],[(true,1)],[(true,4),(true,5)],[(false,3),(false,6)]],#[(0,1),(2,4),(3,0),(6,0),(0,5),(0,5),(6,0)]⟩,#[(.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .leaf) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch .empty .leaf) (.branch (.branch .leaf .leaf) .empty)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))))),(.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch .empty .leaf))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)))),(.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)),(.branch .empty (.branch .leaf (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty))),(.branch (.branch .empty .leaf) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))),.empty,(.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)))),(.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) .leaf))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) .empty)))),(.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty))]⟩
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
end M9

namespace M10
def codes : List (Option (Fin 25)) := [some 8,some 3,some 11,some 2,some 1,some 13,some 17,some 13,some 24,some 0,some 20,some 11]
def partialTable : PartialMachine := fun s => (codes.getD (index s).val none).map decode
def cert : Cert := ⟨⟨#[[(false,0)],[(true,0)],[(true,1),(true,3)],[(true,2)]],#[(0,1),(0,2),(0,3),(0,2)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(false,2)]],#[(0,1),(2,0),(3,0),(2,0)]⟩,#[.leaf,.empty,(.branch (.branch (.branch .empty .leaf) .empty) .empty),.empty,.empty,(.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) (.branch .empty (.branch (.branch .leaf .leaf) .empty))),(.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),.empty,(.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)]⟩
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
end M10

namespace M11
def codes : List (Option (Fin 25)) := [some 8,some 3,some 11,some 2,some 1,some 13,some 17,some 9,some 24,some 0,some 20,some 11]
def partialTable : PartialMachine := fun s => (codes.getD (index s).val none).map decode
def cert : Cert := ⟨⟨#[[(false,0)],[(true,0)],[(true,1),(true,3)],[(true,2)]],#[(0,1),(0,2),(0,3),(0,2)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(false,2)]],#[(0,1),(2,0),(3,0),(2,0)]⟩,#[.leaf,.empty,(.branch (.branch (.branch .empty .leaf) .empty) .empty),.empty,.empty,(.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty),(.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),.empty,(.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)]⟩
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
end M11

namespace M12
def codes : List (Option (Fin 25)) := [some 8,some 3,some 11,some 2,some 1,some 13,some 17,some 13,some 24,some 0,some 20,some 4]
def partialTable : PartialMachine := fun s => (codes.getD (index s).val none).map decode
def cert : Cert := ⟨⟨#[[(false,0)],[(true,0)],[(true,1),(true,3)],[(true,2)]],#[(0,1),(0,2),(0,3),(0,2)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(false,2)]],#[(0,1),(2,0),(3,0),(2,0)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty),.empty,(.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty),.empty,.empty,(.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) (.branch .empty (.branch (.branch .leaf .leaf) .empty))),(.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),.empty,(.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)]⟩
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
end M12

namespace M13
def codes : List (Option (Fin 25)) := [some 8,some 3,some 11,some 2,some 1,some 13,some 17,some 9,some 24,some 0,some 20,some 4]
def partialTable : PartialMachine := fun s => (codes.getD (index s).val none).map decode
def cert : Cert := ⟨⟨#[[(false,0)],[(true,0)],[(true,1),(true,3)],[(true,2)]],#[(0,1),(0,2),(0,3),(0,2)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(false,2)]],#[(0,1),(2,0),(3,0),(2,0)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty),.empty,(.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty),.empty,.empty,(.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty),(.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),.empty,(.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)]⟩
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
end M13

namespace M14
def codes : List (Option (Fin 25)) := [some 8,some 3,some 11,some 2,some 1,some 13,some 17,some 0,some 24,some 13,some 18,some 7]
def partialTable : PartialMachine := fun s => (codes.getD (index s).val none).map decode
def cert : Cert := ⟨⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,2)],[(false,2)]],#[(0,1),(2,0),(4,3),(2,0),(0,0)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(false,2)],[(false,3),(false,4)]],#[(0,1),(2,0),(3,0),(4,0),(4,0)]⟩,#[(.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf)))),(.branch .empty (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),.empty,(.branch .empty (.branch .leaf (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)))),.empty,(.branch (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .leaf)),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)))),(.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))]⟩
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
end M14

namespace M15
def codes : List (Option (Fin 25)) := [some 8,some 3,some 11,some 2,some 1,some 13,some 17,some 0,some 24,some 13,some 18,some 2]
def partialTable : PartialMachine := fun s => (codes.getD (index s).val none).map decode
def cert : Cert := ⟨⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,2)]],#[(0,1),(2,0),(0,3),(2,0)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(false,2)],[(false,3),(false,4)]],#[(0,1),(2,0),(3,0),(4,0),(4,0)]⟩,#[(.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) .empty),.empty,(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf)))),.empty,.empty,(.branch .empty (.branch .leaf (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)))),.empty,(.branch (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .leaf)),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)))),(.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))]⟩
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
end M15

namespace M16
def codes : List (Option (Fin 25)) := [some 8,some 3,some 11,some 2,some 1,some 13,some 17,some 23,some 24,some 13,some 6,some 0]
def partialTable : PartialMachine := fun s => (codes.getD (index s).val none).map decode
def cert : Cert := ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,2),(true,18)],[(false,3),(false,21)],[(true,3)],[(false,5)],[(true,6),(true,11)],[(false,2),(false,6),(false,11),(false,18),(false,20)],[(true,8)],[(true,1)],[(false,10)],[(false,7)],[(true,12),(true,15)],[(true,7),(true,21)],[(false,13),(false,14)],[(true,5)],[(true,10),(true,19)],[(false,16),(false,17)],[(true,16),(true,17)],[(false,19)],[(true,20)]],#[(0,1),(2,10),(8,3),(4,5),(0,0),(6,16),(8,7),(12,14),(0,9),(0,0),(11,17),(8,7),(0,13),(15,0),(15,0),(0,13),(18,19),(18,19),(8,3),(20,17),(8,21),(4,14)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(false,2)],[(true,1)],[(false,4)],[(true,5),(true,6),(true,13)],[(false,3),(false,11),(false,14)],[(true,7)],[(true,2),(true,10)],[(false,8),(false,9)],[(false,10)],[(true,8),(true,9)],[(false,12)],[(false,7)]],#[(0,1),(2,4),(3,9),(7,0),(5,0),(0,6),(0,6),(14,8),(10,12),(10,12),(11,9),(7,0),(13,0),(0,6),(7,0)]⟩,#[(.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) .empty))))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty .leaf))) (.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty))) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch .empty (.branch .leaf (.branch .empty .leaf)))) (.branch (.branch .leaf .leaf) .empty)))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty .leaf)) (.branch .leaf (.branch (.branch .leaf .leaf) .empty))) (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))))) (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty) (.branch .leaf (.branch (.branch .empty .leaf) (.branch .empty .leaf)))) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch (.branch .empty .leaf) .empty))))))),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) .leaf)))) (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .leaf) .empty))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .leaf) .empty)) .empty)) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf)))) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty)))))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .leaf) (.branch .leaf (.branch .empty (.branch .empty (.branch .empty .leaf)))))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch .leaf .leaf) .leaf) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .leaf)) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty)))) .empty))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty)) (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) .empty)))) (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .leaf)) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)) .empty))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch .leaf .leaf))))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))))) (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch .leaf .leaf)) (.branch .empty .leaf))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .leaf) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .leaf) .leaf)) (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .leaf))),(.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)) .empty) (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .leaf)) .empty))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .leaf) (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) .empty)) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch (.branch .empty .leaf) .empty))))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty .leaf) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .empty))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)))) (.branch (.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty))) (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty))))),(.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty))) .empty) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty)) (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .leaf))),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)) .empty) (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .leaf)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty))) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) .empty) (.branch (.branch .leaf (.branch .leaf (.branch .empty (.branch .empty (.branch .empty .leaf))))) .empty))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) (.branch .empty .leaf))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .leaf) (.branch .empty .leaf)) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))))) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch (.branch .empty .leaf) .empty))))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .leaf (.branch .empty (.branch .empty (.branch .empty .leaf))))) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))) (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .leaf)) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .leaf) .empty)))),.empty]⟩
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
end M16

namespace M17
def codes : List (Option (Fin 25)) := [some 8,some 3,some 11,some 2,some 1,some 13,some 17,some 19,some 24,some 15,some 4,some 0]
def partialTable : PartialMachine := fun s => (codes.getD (index s).val none).map decode
def cert : Cert := ⟨⟨#[[(false,0)],[(true,0)],[(true,1),(true,3)],[(true,2)],[(false,3)],[(true,4)],[(false,1)],[(false,2)]],#[(0,1),(6,2),(7,3),(4,2),(0,5),(0,0),(0,0),(0,0)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(false,2)],[(true,3),(true,17)],[(true,4)],[(true,5),(true,8)],[(false,6)],[(true,6)],[(true,1),(true,16)],[(false,9),(false,13)],[(false,10)],[(true,11)],[(true,12),(true,14)],[(true,13)],[(false,14),(false,16)],[(true,9)],[(false,15)]],#[(0,1),(2,9),(3,0),(0,4),(0,5),(0,6),(7,8),(0,0),(0,6),(10,16),(11,0),(0,12),(0,13),(10,14),(15,13),(17,0),(15,9),(0,4)]⟩,#[(.branch (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) .empty)) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) .leaf)) (.branch .leaf (.branch .leaf (.branch .empty .leaf))))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .leaf .leaf))) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch .leaf .leaf)))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf))) (.branch .leaf (.branch (.branch .leaf .leaf) (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty (.branch .leaf .leaf))))) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf)))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .leaf) .empty)) (.branch .empty (.branch (.branch .leaf (.branch .leaf .leaf)) .empty))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))))),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty))) .empty)) (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch .empty (.branch .leaf .leaf)))))),.empty,(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty) (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty))) (.branch (.branch (.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf))) .empty) (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))) .empty),(.branch .empty (.branch .empty (.branch .leaf (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .leaf (.branch .empty .leaf)) .leaf)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty),.empty]⟩
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
end M17
end BB6.Agent13.Box33D17V24PairBlocks
