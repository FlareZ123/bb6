import ZipThreeHoleAudit
import NGramCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent24Raw45Depth3Full1
open BB6Coverage BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent13BlankDelay
open BB6.Agent1NGram

/-- Depth-three Raw45 residual with four undefined rows A1,E0,F0,F1. -/
def parent : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => none
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨true,false,1⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => some (some ⟨true,false,4⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨true,true,1⟩)
  | (4,false) => none
  | (4,true) => some (some ⟨false,true,4⟩)
  | (5,false) => none
  | (5,true) => none
  | _ => none

theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem parent_nohalt : weightedTNFNoAssignedHalt parent := by
  intro slot
  rcases slot with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

/-- Sole 5000-step survivor of the exact audit. A width-one n-gram invariant
    proves nonhalting uniformly over the remaining A1 row. -/
def ngramP : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => none
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨true,false,1⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => some (some ⟨true,false,4⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨true,true,1⟩)
  | (4,false) => some (some ⟨false,false,5⟩)
  | (4,true) => some (some ⟨false,true,4⟩)
  | (5,false) => some (some ⟨true,true,4⟩)
  | (5,true) => some (some ⟨true,false,5⟩)
  | _ => none
def ngramC : Cert := ⟨0,0xf,0xd,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf))]⟩
theorem ngram_ok : check ngramP ngramC = true := by decide
theorem ngram_never (m : Machine) (hm : compatible ngramP m) : NeverHalts m :=
  never ngramP ngramC ngram_ok m hm

/-- Exact proof-carrying cut: 17 splits, 371 side cycles, 20 last-hole leaves,
    and one n-gram-proven leaf. The latest first-hole query is step 29. -/
def tree : Audit :=
  .split 16 (4,false) (byMove [
      .cycle 0 17 true (-1),
      .cycle 12 14 true (0),
      .cycle 18 1 false (4),
      .cycle 17 1 false (3),
      .cycle 16 1 false (4),
      .split 17 (5,false) (byMove [
            .cycle 0 18 true (-1),
            .cycle 12 15 true (0),
            .cycle 19 1 false (3),
            .cycle 18 1 false (2),
            .cycle 16 2 false (4),
            .cycle 17 1 false (3),
            .cycle 0 18 true (-1),
            .cycle 12 15 true (0),
            .cycle 19 1 false (5),
            .cycle 18 1 false (4),
            .cycle 16 2 true (3),
            .cycle 17 1 true (3),
            .cycle 13 10 true (1),
            .cycle 14 6 true (2),
            .cycle 1 19 true (-1),
            .cycle 18 1 false (2),
            .cycle 16 2 false (4),
            .cycle 17 1 false (3),
            .cycle 11 20 true (-1),
            .cycle 1 17 true (-1),
            .cycle 12 14 true (0),
            .cycle 13 11 true (1),
            .split 19 (5,true) (byMove [
                    .cycle 0 20 true (-1),
                    .cycle 12 17 true (0),
                    .cycle 21 1 false (3),
                    .cycle 20 1 false (2),
                    .cycle 16 4 false (4),
                    .cycle 17 3 false (4),
                    .cycle 0 20 true (-1),
                    .cycle 12 17 true (0),
                    .cycle 21 1 false (5),
                    .cycle 20 1 false (4),
                    .cycle 16 4 true (3),
                    .cycle 17 3 true (3),
                    .cycle 13 12 true (1),
                    .cycle 14 8 true (2),
                    .cycle 1 21 true (-1),
                    .cycle 20 1 false (2),
                    .cycle 16 4 false (4),
                    .proven ngramP ngram_never,
                    .cycle 11 22 true (-1),
                    .cycle 1 19 true (-1),
                    .cycle 12 16 true (0),
                    .cycle 13 13 true (1),
                    .cycle 18 2 true (3),
                    .cycle 17 3 true (3)
                  ]),
            .cycle 17 1 true (3)
          ]),
      .cycle 0 17 true (-1),
      .cycle 12 14 true (0),
      .cycle 18 1 false (6),
      .cycle 17 1 false (5),
      .cycle 16 1 true (4),
      .split 17 (5,false) (byMove [
            .cycle 0 18 true (-1),
            .cycle 12 15 true (0),
            .cycle 19 1 false (5),
            .cycle 18 1 false (4),
            .cycle 16 2 true (4),
            .cycle 17 1 false (5),
            .cycle 0 18 true (-1),
            .cycle 12 15 true (0),
            .cycle 19 1 false (7),
            .cycle 18 1 false (6),
            .cycle 16 2 true (4),
            .cycle 17 1 true (5),
            .cycle 13 10 true (1),
            .cycle 14 6 true (2),
            .cycle 1 19 true (-1),
            .cycle 18 1 false (4),
            .split 19 (5,true) (byMove [
                    .cycle 0 20 true (-1),
                    .cycle 12 17 true (0),
                    .cycle 21 1 false (5),
                    .cycle 20 1 false (4),
                    .cycle 16 4 true (4),
                    .cycle 17 3 false (5),
                    .cycle 0 20 true (-1),
                    .cycle 12 17 true (0),
                    .cycle 21 1 false (7),
                    .cycle 20 1 false (6),
                    .cycle 16 4 true (4),
                    .cycle 17 3 true (4),
                    .cycle 13 12 true (1),
                    .cycle 14 8 true (2),
                    .cycle 1 21 true (-1),
                    .cycle 20 1 false (4),
                    .cycle 18 2 true (4),
                    .cycle 17 3 false (5),
                    .cycle 11 22 true (-1),
                    .cycle 1 19 true (-1),
                    .cycle 12 16 true (0),
                    .cycle 13 13 true (1),
                    .cycle 16 4 true (4),
                    .cycle 14 7 true (2)
                  ]),
            .cycle 17 1 false (5),
            .cycle 11 20 true (-1),
            .cycle 1 17 true (-1),
            .cycle 12 14 true (0),
            .cycle 13 11 true (1),
            .cycle 16 2 true (4),
            .cycle 17 1 true (5)
          ]),
      .cycle 13 9 true (1),
      .cycle 14 5 true (2),
      .cycle 1 18 true (-1),
      .cycle 17 1 false (3),
      .cycle 16 1 false (4),
      .split 17 (5,false) (byMove [
            .cycle 14 7 true (2),
            .cycle 1 20 true (-1),
            .cycle 19 1 false (3),
            .cycle 18 1 false (2),
            .cycle 16 2 false (4),
            .cycle 17 1 false (3),
            .split 18 (0,true) (byMove [
                    .cycle 0 19 true (-1),
                    .cycle 12 16 true (0),
                    .cycle 20 1 false (4),
                    .cycle 19 1 false (3),
                    .cycle 16 3 false (4),
                    .cycle 0 20 true (-1),
                    .cycle 0 19 true (-1),
                    .cycle 12 16 true (0),
                    .cycle 20 1 false (6),
                    .cycle 19 1 false (5),
                    .cycle 16 3 true (3),
                    .cycle 0 20 true (-1),
                    .cycle 13 11 true (1),
                    .cycle 14 7 true (2),
                    .cycle 1 20 true (-1),
                    .cycle 19 1 false (3),
                    .cycle 16 3 false (4),
                    .cycle 17 2 true (3),
                    .cycle 11 21 true (-1),
                    .cycle 1 18 true (-1),
                    .cycle 12 15 true (0),
                    .cycle 13 12 true (1),
                    .last 20 (5,true),
                    .cycle 0 20 true (-1)
                  ]),
            .cycle 14 7 true (2),
            .cycle 16 3 false (4),
            .cycle 1 18 true (-1),
            .cycle 15 3 true (3),
            .split 18 (5,true) (byMove [
                    .cycle 0 19 true (-1),
                    .cycle 12 16 true (0),
                    .cycle 20 1 false (4),
                    .cycle 19 1 false (3),
                    .cycle 16 3 false (4),
                    .cycle 19 1 true (3),
                    .cycle 0 19 true (-1),
                    .cycle 12 16 true (0),
                    .cycle 20 1 false (6),
                    .cycle 19 1 false (5),
                    .cycle 16 3 true (3),
                    .cycle 19 1 true (5),
                    .cycle 13 11 true (1),
                    .cycle 14 7 true (2),
                    .cycle 1 20 true (-1),
                    .cycle 19 1 false (3),
                    .cycle 16 3 false (4),
                    .cycle 17 2 true (3),
                    .cycle 11 21 true (-1),
                    .cycle 1 18 true (-1),
                    .cycle 12 15 true (0),
                    .cycle 13 12 true (1),
                    .cycle 15 6 true (3),
                    .cycle 19 1 true (5)
                  ]),
            .cycle 12 11 true (0),
            .cycle 13 7 true (1),
            .cycle 13 11 true (1),
            .cycle 18 1 false (2),
            .cycle 16 2 false (4),
            .cycle 17 1 false (3),
            .split 18 (0,true) (byMove [
                    .cycle 0 20 true (-1),
                    .cycle 14 8 true (2),
                    .cycle 16 4 false (4),
                    .cycle 1 19 true (-1),
                    .cycle 15 4 true (3),
                    .last 19 (5,true),
                    .cycle 0 19 true (-1),
                    .cycle 12 16 true (0),
                    .cycle 7 17 true (-1),
                    .cycle 12 14 true (0),
                    .cycle 16 3 true (3),
                    .cycle 11 22 true (-1),
                    .cycle 12 13 true (0),
                    .cycle 13 9 true (1),
                    .cycle 16 4 false (4),
                    .cycle 13 11 true (1),
                    .cycle 14 5 true (2),
                    .last 19 (5,true),
                    .cycle 11 23 true (-1),
                    .cycle 11 20 true (-1),
                    .cycle 2 17 true (-1),
                    .cycle 12 14 true (0),
                    .last 20 (5,true),
                    .cycle 11 26 true (-1)
                  ]),
            .cycle 13 9 true (1),
            .cycle 14 5 true (2),
            .cycle 11 20 true (-1),
            .cycle 15 3 true (3),
            .split 18 (5,true) (byMove [
                    .last 19 (0,true),
                    .cycle 14 8 true (2),
                    .cycle 16 4 false (4),
                    .cycle 1 19 true (-1),
                    .cycle 15 4 true (3),
                    .cycle 20 1 true (2),
                    .cycle 0 19 true (-1),
                    .cycle 12 16 true (0),
                    .cycle 7 17 true (-1),
                    .cycle 12 14 true (0),
                    .cycle 16 3 true (3),
                    .cycle 19 1 true (5),
                    .last 19 (0,true),
                    .cycle 13 9 true (1),
                    .cycle 16 4 false (4),
                    .cycle 13 11 true (1),
                    .cycle 14 5 true (2),
                    .cycle 17 3 false (4),
                    .cycle 11 23 true (-1),
                    .cycle 11 20 true (-1),
                    .cycle 2 17 true (-1),
                    .cycle 12 14 true (0),
                    .cycle 15 6 true (3),
                    .cycle 19 1 true (5)
                  ])
          ]),
      .cycle 11 19 true (-1),
      .cycle 1 16 true (-1),
      .cycle 12 13 true (0),
      .cycle 13 10 true (1),
      .cycle 16 1 true (4),
      .split 17 (5,false) (byMove [
            .split 18 (0,true) (byMove [
                    .cycle 0 19 true (-1),
                    .cycle 12 16 true (0),
                    .cycle 20 1 false (4),
                    .cycle 19 1 false (3),
                    .cycle 16 3 false (5),
                    .cycle 0 20 true (-1),
                    .cycle 0 19 true (-1),
                    .cycle 12 16 true (0),
                    .cycle 20 1 false (6),
                    .cycle 19 1 false (5),
                    .cycle 16 3 true (4),
                    .cycle 0 20 true (-1),
                    .cycle 13 11 true (1),
                    .cycle 14 7 true (2),
                    .cycle 1 20 true (-1),
                    .cycle 19 1 false (3),
                    .last 20 (5,true),
                    .cycle 14 9 true (2),
                    .cycle 11 21 true (-1),
                    .cycle 1 18 true (-1),
                    .cycle 12 15 true (0),
                    .cycle 13 12 true (1),
                    .cycle 16 3 true (4),
                    .cycle 17 2 true (4)
                  ]),
            .cycle 14 7 true (2),
            .split 20 (5,true) (byMove [
                    .last 21 (0,true),
                    .cycle 14 10 true (2),
                    .cycle 18 3 false (4),
                    .cycle 1 21 true (-1),
                    .cycle 15 6 true (3),
                    .cycle 24 1 false (2),
                    .cycle 0 21 true (-1),
                    .cycle 12 18 true (0),
                    .cycle 7 19 true (-1),
                    .cycle 12 16 true (0),
                    .cycle 16 5 true (3),
                    .cycle 12 18 true (0),
                    .last 21 (0,true),
                    .cycle 13 11 true (1),
                    .cycle 18 3 false (4),
                    .cycle 13 13 true (1),
                    .cycle 14 7 true (2),
                    .cycle 24 1 false (2),
                    .cycle 11 25 true (-1),
                    .cycle 11 22 true (-1),
                    .cycle 2 19 true (-1),
                    .cycle 12 16 true (0),
                    .cycle 14 10 true (2),
                    .cycle 14 9 true (2)
                  ]),
            .cycle 1 18 true (-1),
            .cycle 15 3 true (3),
            .split 18 (5,true) (byMove [
                    .cycle 0 19 true (-1),
                    .cycle 12 16 true (0),
                    .cycle 20 1 false (4),
                    .cycle 19 1 false (3),
                    .cycle 16 3 false (5),
                    .cycle 19 1 false (3),
                    .cycle 0 19 true (-1),
                    .cycle 12 16 true (0),
                    .cycle 20 1 false (6),
                    .cycle 19 1 false (5),
                    .cycle 16 3 true (4),
                    .cycle 19 1 false (5),
                    .cycle 13 11 true (1),
                    .cycle 14 7 true (2),
                    .cycle 1 20 true (-1),
                    .cycle 19 1 false (3),
                    .cycle 14 7 true (2),
                    .cycle 19 1 false (3),
                    .cycle 11 21 true (-1),
                    .cycle 1 18 true (-1),
                    .cycle 12 15 true (0),
                    .cycle 13 12 true (1),
                    .cycle 16 3 true (4),
                    .cycle 17 2 true (4)
                  ]),
            .cycle 0 18 true (-1),
            .cycle 12 15 true (0),
            .cycle 7 16 true (-1),
            .cycle 12 13 true (0),
            .cycle 16 2 true (4),
            .cycle 17 1 true (5),
            .split 18 (0,true) (byMove [
                    .cycle 14 8 true (2),
                    .cycle 1 21 true (-1),
                    .cycle 20 1 false (4),
                    .cycle 19 1 false (3),
                    .cycle 16 3 false (5),
                    .last 29 (5,true),
                    .cycle 0 20 true (-1),
                    .cycle 14 8 true (2),
                    .last 21 (5,true),
                    .cycle 1 19 true (-1),
                    .cycle 15 4 true (3),
                    .last 19 (5,true),
                    .cycle 12 12 true (0),
                    .cycle 13 8 true (1),
                    .cycle 13 12 true (1),
                    .cycle 19 1 false (3),
                    .last 20 (5,true),
                    .cycle 7 14 true (-1),
                    .cycle 11 24 true (-1),
                    .cycle 13 10 true (1),
                    .cycle 14 6 true (2),
                    .cycle 11 21 true (-1),
                    .cycle 15 4 true (3),
                    .last 19 (5,true)
                  ]),
            .cycle 13 8 true (1),
            .split 20 (5,true) (byMove [
                    .last 21 (0,true),
                    .cycle 14 17 true (2),
                    .cycle 18 3 false (4),
                    .cycle 14 10 true (2),
                    .cycle 15 9 true (3),
                    .cycle 1 27 true (-1),
                    .last 21 (0,true),
                    .cycle 14 10 true (2),
                    .cycle 11 24 true (-1),
                    .cycle 1 21 true (-1),
                    .cycle 15 6 true (3),
                    .cycle 1 24 true (-1),
                    .last 21 (0,true),
                    .cycle 12 12 true (0),
                    .cycle 18 3 false (4),
                    .cycle 12 14 true (0),
                    .cycle 13 8 true (1),
                    .cycle 7 18 true (-1),
                    .last 21 (0,true),
                    .cycle 12 14 true (0),
                    .cycle 14 8 true (2),
                    .cycle 11 25 true (-1),
                    .cycle 15 6 true (3),
                    .cycle 13 11 true (1)
                  ]),
            .cycle 13 10 true (1),
            .cycle 14 4 true (2),
            .split 18 (5,true) (byMove [
                    .cycle 14 8 true (2),
                    .cycle 1 21 true (-1),
                    .cycle 20 1 false (4),
                    .cycle 19 1 false (3),
                    .cycle 16 3 false (5),
                    .cycle 19 1 false (3),
                    .last 19 (0,true),
                    .cycle 14 8 true (2),
                    .cycle 7 20 true (-1),
                    .cycle 1 19 true (-1),
                    .cycle 15 4 true (3),
                    .cycle 20 1 false (6),
                    .cycle 12 12 true (0),
                    .cycle 13 8 true (1),
                    .cycle 13 12 true (1),
                    .cycle 19 1 false (3),
                    .cycle 13 8 true (1),
                    .cycle 19 1 false (3),
                    .last 19 (0,true),
                    .cycle 13 10 true (1),
                    .cycle 14 6 true (2),
                    .cycle 11 21 true (-1),
                    .cycle 15 4 true (3),
                    .cycle 17 3 true (4)
                  ]),
            .cycle 11 22 true (-1),
            .cycle 11 19 true (-1),
            .cycle 2 16 true (-1),
            .cycle 12 13 true (0),
            .cycle 16 2 true (4),
            .cycle 17 1 true (5)
          ])
    ])

theorem checked : zipCheck 35 parent tree = true := by decide +kernel

noncomputable def certificate : WeightedTNFCertificate 35 parent 6 :=
  certifiedZip 35 parent tree parent_root parent_nohalt checked

theorem all_completions_weighted : ∀ m, compatible parent m → WeightedBound 35 m :=
  certificate.sound

theorem cover : Cover (WeightedBound 35) parent :=
  Cover.leaf _ all_completions_weighted

#print axioms ngram_never
#print axioms checked
#print axioms all_completions_weighted
#print axioms cover
end BB6.Agent24Raw45Depth3Full1
