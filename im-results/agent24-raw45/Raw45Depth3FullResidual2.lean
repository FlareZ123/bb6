import ZipThreeHoleAudit
import NGramCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent24Raw45Depth3Full2
open BB6Coverage BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent13BlankDelay
open BB6.Agent1NGram

/-- Depth-three Raw45 residual with four undefined rows A1,C1,F0,F1. -/
def parent : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => none
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨true,true,4⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => none
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨true,true,1⟩)
  | (4,false) => some (some ⟨false,true,5⟩)
  | (4,true) => some (some ⟨false,false,4⟩)
  | (5,false) => none
  | (5,true) => none
  | _ => none

theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem parent_nohalt : weightedTNFNoAssignedHalt parent := by
  intro slot
  rcases slot with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

/-- Sole 5000-step survivor: F0=1LE,F1=1RF while A1,C1 remain open.
    A width-three n-gram invariant proves every completion nonhalting. -/
def ngramP : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => none
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨true,true,4⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => none
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨true,true,1⟩)
  | (4,false) => some (some ⟨false,true,5⟩)
  | (4,true) => some (some ⟨false,false,4⟩)
  | (5,false) => some (some ⟨true,false,4⟩)
  | (5,true) => some (some ⟨true,true,5⟩)
  | _ => none
def ngramC : Cert := ⟨2,0xd045,0xffff,#[.leaf,.empty,(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) .empty),.empty,(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf))))),(.branch .empty (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) (.branch .leaf (.branch .leaf (.branch .leaf .leaf)))) (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) (.branch .leaf (.branch .leaf (.branch .leaf .leaf))))) (.branch (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) (.branch .leaf (.branch .leaf (.branch .leaf .leaf)))) (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) (.branch .leaf (.branch .leaf (.branch .leaf .leaf)))))),(.branch (.branch (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) (.branch .leaf (.branch .leaf (.branch .leaf .leaf)))) (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) (.branch .leaf (.branch .leaf (.branch .leaf .leaf))))) (.branch (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) (.branch .leaf (.branch .leaf (.branch .leaf .leaf)))) (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) (.branch .leaf (.branch .leaf (.branch .leaf .leaf)))))),(.branch (.branch (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) (.branch .leaf (.branch .leaf (.branch .leaf .leaf)))) (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) (.branch .leaf (.branch .leaf (.branch .leaf .leaf))))) (.branch (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) (.branch .leaf (.branch .leaf (.branch .leaf .leaf)))) (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) (.branch .leaf (.branch .leaf (.branch .leaf .leaf))))))]⟩
theorem ngram_ok : check ngramP ngramC = true := by decide
theorem ngram_never (m : Machine) (hm : compatible ngramP m) : NeverHalts m :=
  never ngramP ngramC ngram_ok m hm

/-- Exact proof-carrying cut: 8 splits, 173 side cycles, 11 last-hole leaves,
    and one n-gram-proven two-hole leaf. Latest first-hole query is step 36. -/
def tree : Audit :=
  .split 12 (5,false) (byMove [
      .cycle 0 13 false (3),
      .cycle 8 11 false (2),
      .cycle 14 1 false (0),
      .cycle 13 1 false (-1),
      .cycle 11 2 true (-1),
      .cycle 12 1 false (0),
      .cycle 0 13 true (-1),
      .cycle 8 11 true (-1),
      .cycle 14 1 false (2),
      .cycle 13 1 false (1),
      .cycle 11 2 true (-1),
      .cycle 12 1 true (0),
      .cycle 11 4 true (-1),
      .split 14 (2,true) (byMove [
            .split 15 (0,true) (byMove [
                    .cycle 0 16 false (3),
                    .cycle 8 14 false (2),
                    .cycle 17 1 false (-1),
                    .cycle 16 1 false (-2),
                    .cycle 11 5 false (0),
                    .cycle 12 4 false (0),
                    .cycle 0 16 true (-1),
                    .cycle 8 14 true (-1),
                    .cycle 17 1 false (1),
                    .cycle 16 1 false (0),
                    .cycle 11 5 true (-1),
                    .cycle 12 4 true (-1),
                    .cycle 8 19 false (2),
                    .cycle 13 3 false (0),
                    .cycle 1 17 false (3),
                    .cycle 16 1 false (-2),
                    .last 17 (5,true),
                    .cycle 12 4 false (0),
                    .cycle 7 17 false (3),
                    .cycle 1 15 false (3),
                    .cycle 8 13 false (2),
                    .cycle 11 8 true (-1),
                    .cycle 11 5 true (-1),
                    .cycle 9 9 false (1)
                  ]),
            .cycle 11 5 true (-1),
            .cycle 17 1 false (-1),
            .cycle 1 15 false (3),
            .cycle 10 5 false (0),
            .split 15 (5,true) (byMove [
                    .cycle 0 16 false (3),
                    .cycle 8 14 false (2),
                    .cycle 17 1 false (-1),
                    .cycle 16 1 false (-2),
                    .cycle 11 5 false (0),
                    .cycle 12 4 false (0),
                    .cycle 0 16 true (-1),
                    .cycle 8 14 true (-1),
                    .cycle 17 1 false (1),
                    .cycle 16 1 false (0),
                    .cycle 11 5 true (-1),
                    .cycle 12 4 true (-1),
                    .last 23 (0,true),
                    .cycle 13 3 false (0),
                    .cycle 1 17 false (3),
                    .cycle 16 1 false (-2),
                    .cycle 15 2 true (-2),
                    .cycle 12 4 false (0),
                    .cycle 7 17 false (3),
                    .cycle 1 15 false (3),
                    .cycle 8 13 false (2),
                    .cycle 11 8 true (-1),
                    .cycle 11 5 true (-1),
                    .cycle 9 9 false (1)
                  ]),
            .cycle 0 15 true (-1),
            .cycle 8 13 true (-1),
            .cycle 8 13 false (2),
            .cycle 8 11 false (2),
            .cycle 11 4 true (-1),
            .cycle 12 3 true (-1),
            .split 15 (0,true) (byMove [
                    .cycle 0 42 false (3),
                    .last 36 (5,true),
                    .cycle 17 1 false (-1),
                    .cycle 16 1 false (-2),
                    .cycle 11 5 false (0),
                    .cycle 12 4 false (0),
                    .cycle 0 17 true (-1),
                    .cycle 11 6 true (-1),
                    .cycle 11 8 true (-1),
                    .cycle 1 16 true (-1),
                    .cycle 10 6 true (-1),
                    .last 16 (5,true),
                    .cycle 8 10 false (2),
                    .cycle 13 3 false (0),
                    .cycle 8 21 false (2),
                    .cycle 16 1 false (-2),
                    .last 17 (5,true),
                    .cycle 12 4 false (0),
                    .cycle 7 19 false (4),
                    .cycle 11 6 true (-1),
                    .cycle 14 2 true (-1),
                    .cycle 7 17 false (3),
                    .cycle 9 7 false (1),
                    .last 16 (5,true)
                  ]),
            .cycle 9 7 false (1),
            .cycle 8 21 false (2),
            .cycle 11 6 true (-1),
            .cycle 10 5 false (0),
            .split 15 (5,true) (byMove [
                    .last 20 (0,true),
                    .cycle 1 36 false (3),
                    .cycle 17 1 false (-1),
                    .cycle 16 1 false (-2),
                    .cycle 11 5 false (0),
                    .cycle 12 4 false (0),
                    .last 16 (0,true),
                    .cycle 11 6 true (-1),
                    .cycle 12 5 false (0),
                    .cycle 1 16 true (-1),
                    .cycle 10 6 true (-1),
                    .cycle 12 5 true (-1),
                    .cycle 8 10 false (2),
                    .cycle 13 3 false (0),
                    .cycle 8 21 false (2),
                    .cycle 16 1 false (-2),
                    .cycle 15 2 true (-2),
                    .cycle 12 4 false (0),
                    .last 16 (0,true),
                    .cycle 11 6 true (-1),
                    .cycle 14 2 true (-1),
                    .cycle 7 17 false (3),
                    .cycle 9 7 false (1),
                    .cycle 8 11 false (2)
                  ]),
            .cycle 7 17 false (4),
            .cycle 7 15 false (3),
            .cycle 2 13 false (3),
            .cycle 11 7 true (-1),
            .cycle 11 4 true (-1),
            .cycle 8 9 false (2)
          ]),
      .cycle 1 14 true (-1),
      .cycle 13 1 false (-1),
      .split 14 (5,true) (byMove [
            .cycle 0 15 false (3),
            .cycle 8 13 false (2),
            .cycle 16 1 false (0),
            .cycle 15 1 false (-1),
            .cycle 11 4 true (-1),
            .cycle 12 3 false (0),
            .cycle 0 15 true (-1),
            .cycle 8 13 true (-1),
            .cycle 16 1 false (2),
            .cycle 15 1 false (1),
            .cycle 11 4 true (-1),
            .cycle 12 3 true (-1),
            .cycle 11 6 true (-1),
            .split 16 (2,true) (byMove [
                    .last 17 (0,true),
                    .cycle 11 7 true (-1),
                    .cycle 19 1 false (-1),
                    .cycle 1 17 false (3),
                    .cycle 10 7 false (0),
                    .cycle 14 3 false (0),
                    .cycle 0 17 true (-1),
                    .cycle 8 15 true (-1),
                    .cycle 8 15 false (2),
                    .cycle 8 13 false (2),
                    .cycle 11 6 true (-1),
                    .cycle 12 5 true (-1),
                    .last 17 (0,true),
                    .cycle 9 9 false (1),
                    .cycle 8 25 false (2),
                    .cycle 11 8 true (-1),
                    .cycle 10 7 false (0),
                    .cycle 14 3 false (0),
                    .cycle 7 19 false (4),
                    .cycle 7 17 false (3),
                    .cycle 2 15 false (3),
                    .cycle 11 9 true (-1),
                    .cycle 11 6 true (-1),
                    .cycle 9 9 false (1)
                  ]),
            .cycle 1 16 true (-1),
            .cycle 15 1 false (-1),
            .cycle 13 2 true (-1),
            .cycle 12 3 false (0),
            .cycle 7 16 true (-1),
            .cycle 1 14 true (-1),
            .cycle 8 12 true (-1),
            .cycle 11 7 true (-1),
            .cycle 11 4 true (-1),
            .proven ngramP ngram_never
          ]),
      .cycle 12 1 false (0),
      .cycle 7 14 true (-1),
      .cycle 1 12 true (-1),
      .cycle 8 10 true (-1),
      .cycle 11 5 true (-1),
      .cycle 11 2 true (-1),
      .cycle 12 1 true (0)
    ])

theorem checked : zipCheck 42 parent tree = true := by decide +kernel
noncomputable def certificate : WeightedTNFCertificate 42 parent 6 :=
  certifiedZip 42 parent tree parent_root parent_nohalt checked
theorem all_completions_weighted : ∀ m, compatible parent m → WeightedBound 42 m :=
  certificate.sound
theorem cover : Cover (WeightedBound 42) parent := Cover.leaf _ all_completions_weighted

#print axioms ngram_never
#print axioms checked
#print axioms all_completions_weighted
#print axioms cover
end BB6.Agent24Raw45Depth3Full2
