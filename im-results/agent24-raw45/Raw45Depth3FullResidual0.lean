import ZipThreeHoleAudit
import NGramCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent24Raw45Depth3Full0
open BB6Coverage BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent13BlankDelay
open BB6.Agent1NGram

/-- A depth-three Raw45 residual selected from the exact reproduced first-use frontier.
    Four rows remain undefined: A1, C1, E0, F1. -/
def parent : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => none
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨false,true,4⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => none
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨true,true,1⟩)
  | (4,false) => none
  | (4,true) => some (some ⟨false,false,5⟩)
  | (5,false) => some (some ⟨false,false,1⟩)
  | (5,true) => none
  | _ => none

theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem parent_nohalt : weightedTNFNoAssignedHalt parent := by
  intro slot
  rcases slot with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

/-- The sole 5000-step survivor of the exact finite audit tree.
    A width-one source-sound n-gram invariant proves it never halts for every
    completion of the remaining A1 row. -/
def ngramP : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => none
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨false,true,4⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => some (some ⟨false,false,5⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨true,true,1⟩)
  | (4,false) => some (some ⟨true,false,1⟩)
  | (4,true) => some (some ⟨false,false,5⟩)
  | (5,false) => some (some ⟨false,false,1⟩)
  | (5,true) => some (some ⟨true,false,2⟩)
  | _ => none
def ngramC : Cert := ⟨0,0xf,0xf,#[.leaf,.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty)]⟩
theorem ngram_ok : check ngramP ngramC = true := by decide
theorem ngram_never (m : Machine) (hm : compatible ngramP m) : NeverHalts m :=
  never ngramP ngramC ngram_ok m hm

/-- Exact proof-carrying cut: 8 split nodes, 171 side-cycle leaves,
    13 one-hole leaves, and one n-gram-proven leaf. -/
def tree : Audit :=
  .split 10 (4,false) (byMove [
      .cycle 0 11 true (0),
      .cycle 1 10 true (1),
      .cycle 21 1 false (1),
      .cycle 9 4 true (0),
      .cycle 23 1 false (-1),
      .cycle 11 11 false (1),
      .cycle 0 11 true (0),
      .cycle 1 10 true (1),
      .cycle 9 15 true (0),
      .cycle 20 1 false (2),
      .cycle 10 1 true (2),
      .cycle 1 11 true (1),
      .cycle 9 3 true (1),
      .split 12 (2,true) (byMove [
            .split 13 (0,true) (byMove [
                    .cycle 0 15 false (3),
                    .cycle 14 13 false (1),
                    .cycle 0 15 false (3),
                    .cycle 1 14 true (0),
                    .cycle 25 4 false (-1),
                    .last 14 (5,true),
                    .cycle 0 14 true (0),
                    .cycle 1 13 true (1),
                    .cycle 28 1 false (2),
                    .cycle 25 1 false (1),
                    .cycle 10 4 true (1),
                    .cycle 1 14 true (1),
                    .cycle 9 16 false (2),
                    .cycle 27 3 false (0),
                    .cycle 11 5 false (2),
                    .cycle 9 6 true (0),
                    .cycle 25 4 false (-1),
                    .last 14 (5,true),
                    .cycle 0 14 true (0),
                    .cycle 1 13 true (1),
                    .cycle 2 12 true (1),
                    .cycle 9 7 true (1),
                    .cycle 15 17 false (2),
                    .cycle 8 6 true (1)
                  ]),
            .cycle 9 4 true (1),
            .cycle 16 1 false (0),
            .cycle 1 13 true (1),
            .split 14 (5,true) (byMove [
                    .cycle 0 15 false (3),
                    .cycle 15 14 false (1),
                    .cycle 16 1 false (0),
                    .cycle 15 1 false (-1),
                    .cycle 15 14 false (-1),
                    .cycle 15 14 false (0),
                    .cycle 0 15 true (0),
                    .cycle 15 14 false (3),
                    .cycle 16 1 false (2),
                    .cycle 15 1 false (1),
                    .cycle 15 14 false (1),
                    .cycle 15 14 false (2),
                    .cycle 9 7 false (2),
                    .cycle 15 14 false (0),
                    .cycle 1 16 true (-1),
                    .cycle 15 1 false (-1),
                    .cycle 15 14 false (-1),
                    .cycle 33 14 false (-1),
                    .cycle 0 15 true (0),
                    .cycle 1 14 true (0),
                    .cycle 15 14 false (2),
                    .cycle 9 8 true (0),
                    .cycle 17 14 false (1),
                    .cycle 15 14 false (1)
                  ]),
            .split 13 (5,true) (byMove [
                    .last 14 (0,true),
                    .cycle 14 13 false (1),
                    .cycle 30 1 false (-2),
                    .cycle 1 14 true (0),
                    .cycle 25 4 false (-1),
                    .cycle 14 14 false (0),
                    .cycle 0 14 true (0),
                    .cycle 1 13 true (1),
                    .cycle 28 1 false (2),
                    .cycle 25 1 false (1),
                    .cycle 10 4 true (1),
                    .cycle 1 14 true (1),
                    .last 14 (0,true),
                    .cycle 27 3 false (0),
                    .proven ngramP ngram_never,
                    .cycle 9 6 true (0),
                    .cycle 25 4 false (-1),
                    .cycle 21 14 false (2),
                    .cycle 0 14 true (0),
                    .cycle 1 13 true (1),
                    .cycle 2 12 true (1),
                    .cycle 9 7 true (1),
                    .cycle 15 17 false (2),
                    .cycle 8 6 true (1)
                  ]),
            .cycle 0 13 true (0),
            .cycle 1 12 true (1),
            .cycle 1 26 true (1),
            .cycle 3 10 true (1),
            .cycle 10 3 true (1),
            .cycle 1 13 true (1),
            .split 13 (0,true) (byMove [
                    .cycle 1 18 true (-1),
                    .cycle 9 13 true (-1),
                    .cycle 9 7 false (2),
                    .cycle 11 4 true (0),
                    .cycle 25 4 false (-1),
                    .last 14 (5,true),
                    .cycle 0 15 true (0),
                    .cycle 9 5 true (1),
                    .cycle 9 7 true (1),
                    .cycle 1 14 true (1),
                    .cycle 14 15 false (2),
                    .last 14 (5,true),
                    .cycle 14 9 false (1),
                    .cycle 27 3 false (0),
                    .cycle 9 17 false (2),
                    .cycle 23 1 false (-1),
                    .cycle 25 4 false (-1),
                    .last 14 (5,true),
                    .cycle 0 15 true (0),
                    .cycle 9 5 true (1),
                    .cycle 12 2 true (1),
                    .cycle 1 14 true (1),
                    .last 15 (5,true),
                    .last 14 (5,true)
                  ]),
            .cycle 13 15 false (2),
            .cycle 9 18 true (-1),
            .cycle 9 5 true (1),
            .split 14 (5,true) (byMove [
                    .cycle 1 18 true (-1),
                    .cycle 15 14 false (1),
                    .cycle 16 1 false (0),
                    .cycle 15 1 false (-1),
                    .cycle 15 14 false (-1),
                    .cycle 15 14 false (0),
                    .cycle 9 7 true (0),
                    .cycle 15 14 false (2),
                    .cycle 1 16 true (0),
                    .cycle 15 1 false (1),
                    .cycle 15 14 false (1),
                    .cycle 1 18 true (0),
                    .cycle 9 7 false (2),
                    .cycle 15 14 false (0),
                    .cycle 11 6 true (-1),
                    .cycle 15 1 false (-1),
                    .cycle 15 14 false (-1),
                    .cycle 23 14 false (-1),
                    .cycle 9 7 true (0),
                    .cycle 11 4 true (0),
                    .cycle 1 16 true (0),
                    .cycle 15 14 false (2),
                    .cycle 17 14 false (1),
                    .cycle 15 14 false (1)
                  ]),
            .split 13 (5,true) (byMove [
                    .last 14 (0,true),
                    .cycle 9 13 true (-1),
                    .cycle 30 1 false (-2),
                    .cycle 11 4 true (0),
                    .cycle 25 4 false (-1),
                    .cycle 14 14 false (0),
                    .last 14 (0,true),
                    .cycle 9 5 true (1),
                    .cycle 9 17 true (-1),
                    .cycle 1 14 true (1),
                    .cycle 14 15 false (2),
                    .cycle 1 15 true (1),
                    .last 14 (0,true),
                    .cycle 27 3 false (0),
                    .cycle 9 44 false (2),
                    .cycle 23 1 false (-1),
                    .cycle 25 4 false (-1),
                    .cycle 14 18 false (2),
                    .last 14 (0,true),
                    .cycle 9 5 true (1),
                    .cycle 12 2 true (1),
                    .cycle 1 14 true (1),
                    .cycle 17 19 false (2),
                    .cycle 8 7 true (1)
                  ]),
            .cycle 0 13 true (0),
            .cycle 1 12 true (1),
            .cycle 2 11 true (1),
            .cycle 9 6 true (1),
            .cycle 6 8 true (1),
            .cycle 8 5 true (1)
          ]),
      .cycle 1 12 true (1),
      .cycle 18 1 false (0),
      .cycle 23 1 false (-1),
      .cycle 9 9 true (-1),
      .cycle 0 11 true (0),
      .cycle 1 10 true (1),
      .cycle 2 9 true (1),
      .cycle 9 4 true (1),
      .cycle 10 1 true (2),
      .cycle 8 3 true (1)
    ])
theorem checked : zipCheck 21 parent tree = true := by decide +kernel

noncomputable def certificate : WeightedTNFCertificate 21 parent 6 :=
  certifiedZip 21 parent tree parent_root parent_nohalt checked

/-- Every full completion of this four-hole Raw45 residual either never halts
    or halts with weighted score at most 21. -/
theorem all_completions_weighted : ∀ m, compatible parent m → WeightedBound 21 m :=
  certificate.sound

theorem cover : Cover (WeightedBound 21) parent :=
  Cover.leaf _ all_completions_weighted

#print axioms ngram_never
#print axioms checked
#print axioms all_completions_weighted
#print axioms cover
end BB6.Agent24Raw45Depth3Full0
