import ZipThreeHoleAudit
import NGramCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent24Raw45Depth3Full4
open BB6Coverage BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent13BlankDelay
open BB6.Agent1NGram

def parent : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => none
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨false,false,3⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => some (some ⟨false,false,4⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨true,true,1⟩)
  | (4,false) => none
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

def ngramP : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => none
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨false,false,3⟩)
  | (2,false) => some (some ⟨false,true,3⟩)
  | (2,true) => some (some ⟨false,false,4⟩)
  | (3,false) => some (some ⟨true,false,3⟩)
  | (3,true) => some (some ⟨true,true,1⟩)
  | (4,false) => some (some ⟨false,true,5⟩)
  | (4,true) => some (some ⟨false,false,4⟩)
  | (5,false) => some (some ⟨true,false,4⟩)
  | (5,true) => some (some ⟨true,true,5⟩)
  | _ => none
def ngramC : Cert := ⟨0,0xf,0xf,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf))]⟩
theorem ngram_ok : check ngramP ngramC = true := by decide
theorem ngram_never (m : Machine) (hm : compatible ngramP m) : NeverHalts m :=
  never ngramP ngramC ngram_ok m hm

/-- Exact proof-carrying cut: 16 splits, 348 side cycles, 20 last-hole leaves,
    one width-one n-gram leaf; latest first-hole query step 38. -/
def tree : Audit :=
  .split 13 (4,false) (byMove [
      .cycle 0 14 false (3),
      .cycle 11 12 false (1),
      .cycle 15 1 false (-1),
      .cycle 14 1 false (-2),
      .cycle 13 1 false (-1),
      .split 14 (5,false) (byMove [
            .cycle 0 15 false (3),
            .cycle 11 13 false (1),
            .cycle 16 1 false (-2),
            .cycle 15 1 false (-3),
            .cycle 13 2 false (-1),
            .cycle 14 1 false (-2),
            .cycle 0 15 false (3),
            .cycle 11 13 false (1),
            .cycle 16 1 false (0),
            .cycle 15 1 false (-1),
            .cycle 13 2 true (-2),
            .cycle 14 1 true (-2),
            .cycle 1 17 false (3),
            .cycle 12 5 false (0),
            .cycle 1 16 false (3),
            .cycle 15 1 false (-3),
            .cycle 13 2 false (-1),
            .cycle 14 1 false (-2),
            .cycle 10 16 false (2),
            .cycle 1 14 false (3),
            .cycle 11 12 false (1),
            .cycle 1 18 false (3),
            .split 16 (5,true) (byMove [
                    .cycle 0 17 false (3),
                    .cycle 11 15 false (1),
                    .cycle 18 1 false (-2),
                    .cycle 17 1 false (-3),
                    .cycle 13 4 false (-1),
                    .cycle 14 3 false (-1),
                    .cycle 0 17 false (3),
                    .cycle 11 15 false (1),
                    .cycle 18 1 false (0),
                    .cycle 17 1 false (-1),
                    .cycle 13 4 true (-2),
                    .cycle 14 3 true (-2),
                    .cycle 1 19 false (3),
                    .cycle 12 7 false (0),
                    .cycle 1 18 false (3),
                    .cycle 17 1 false (-3),
                    .cycle 13 4 false (-1),
                    .cycle 11 7 false (1),
                    .cycle 10 18 false (2),
                    .cycle 1 16 false (3),
                    .cycle 11 14 false (1),
                    .cycle 1 20 false (3),
                    .cycle 15 2 true (-2),
                    .cycle 14 3 true (-2)
                  ]),
            .cycle 14 1 true (-2)
          ]),
      .cycle 0 14 true (-1),
      .cycle 11 12 true (-1),
      .cycle 15 1 false (1),
      .cycle 14 1 false (0),
      .cycle 13 1 true (-1),
      .split 14 (5,false) (byMove [
            .cycle 0 15 false (3),
            .cycle 11 13 false (1),
            .cycle 16 1 false (0),
            .cycle 15 1 false (-1),
            .cycle 13 2 true (-1),
            .cycle 14 1 false (0),
            .cycle 0 15 true (-1),
            .cycle 11 13 true (-1),
            .cycle 16 1 false (2),
            .cycle 15 1 false (1),
            .cycle 13 2 true (-1),
            .cycle 14 1 true (0),
            .cycle 1 17 false (3),
            .cycle 12 5 false (0),
            .cycle 1 16 true (-1),
            .cycle 15 1 false (-1),
            .split 16 (5,true) (byMove [
                    .cycle 0 17 false (3),
                    .cycle 11 15 false (1),
                    .cycle 18 1 false (0),
                    .cycle 17 1 false (-1),
                    .cycle 13 4 true (-1),
                    .cycle 14 3 false (0),
                    .cycle 0 17 true (-1),
                    .cycle 11 15 true (-1),
                    .cycle 18 1 false (2),
                    .cycle 17 1 false (1),
                    .cycle 13 4 true (-1),
                    .cycle 14 3 true (-1),
                    .cycle 1 19 false (3),
                    .cycle 12 7 false (0),
                    .cycle 1 18 true (-1),
                    .cycle 17 1 false (-1),
                    .cycle 15 2 true (-1),
                    .cycle 14 3 false (0),
                    .cycle 10 18 true (-1),
                    .cycle 1 16 true (-1),
                    .cycle 11 14 true (-1),
                    .cycle 1 20 true (-1),
                    .cycle 13 4 true (-1),
                    .proven ngramP ngram_never
                  ]),
            .cycle 14 1 false (0),
            .cycle 10 16 true (-1),
            .cycle 1 14 true (-1),
            .cycle 11 12 true (-1),
            .cycle 1 18 true (-1),
            .cycle 13 2 true (-1),
            .cycle 14 1 true (0)
          ]),
      .cycle 1 16 false (3),
      .cycle 12 4 false (0),
      .cycle 1 15 false (3),
      .cycle 14 1 false (-2),
      .cycle 13 1 false (-1),
      .split 14 (5,false) (byMove [
            .cycle 11 7 false (1),
            .split 31 (5,true) (byMove [
                    .cycle 11 24 false (2),
                    .cycle 15 17 false (2),
                    .cycle 33 1 false (-3),
                    .cycle 32 1 false (-4),
                    .cycle 28 11 false (0),
                    .cycle 11 31 false (2),
                    .last 32 (0,true),
                    .cycle 33 1 false (-3),
                    .cycle 13 20 false (2),
                    .cycle 1 32 false (3),
                    .cycle 12 20 false (2),
                    .cycle 11 32 false (2),
                    .cycle 11 26 false (2),
                    .cycle 82 1 false (-8),
                    .cycle 1 35 false (3),
                    .cycle 32 1 false (-4),
                    .cycle 28 13 false (0),
                    .cycle 17 20 false (2),
                    .last 32 (0,true),
                    .cycle 1 33 false (3),
                    .cycle 12 21 false (2),
                    .cycle 10 33 false (2),
                    .cycle 11 21 false (2),
                    .cycle 1 35 false (3)
                  ]),
            .cycle 16 1 false (-2),
            .cycle 15 1 false (-3),
            .cycle 13 2 false (-1),
            .cycle 14 1 false (-2),
            .split 15 (0,true) (byMove [
                    .cycle 0 16 false (3),
                    .cycle 11 14 false (1),
                    .cycle 17 1 false (-1),
                    .cycle 16 1 false (-2),
                    .cycle 13 3 false (-1),
                    .cycle 0 17 false (3),
                    .cycle 0 16 true (-2),
                    .cycle 11 14 true (-2),
                    .cycle 17 1 false (1),
                    .cycle 16 1 false (0),
                    .cycle 13 3 true (-2),
                    .cycle 0 17 true (-2),
                    .cycle 1 18 false (3),
                    .cycle 12 6 false (0),
                    .cycle 1 17 false (3),
                    .cycle 16 1 false (-2),
                    .cycle 13 3 false (-1),
                    .cycle 14 2 true (-2),
                    .cycle 10 17 false (3),
                    .cycle 1 15 false (3),
                    .cycle 11 13 false (1),
                    .cycle 1 19 false (3),
                    .last 17 (5,true),
                    .last 31 (5,true)
                  ]),
            .cycle 16 1 false (-2),
            .cycle 13 3 false (-1),
            .cycle 1 15 false (3),
            .cycle 12 3 false (0),
            .split 15 (5,true) (byMove [
                    .cycle 0 16 false (3),
                    .cycle 11 14 false (1),
                    .cycle 17 1 false (-1),
                    .cycle 16 1 false (-2),
                    .cycle 13 3 false (-1),
                    .cycle 16 1 true (-2),
                    .cycle 0 16 true (-2),
                    .cycle 11 14 true (-2),
                    .cycle 17 1 false (1),
                    .cycle 16 1 false (0),
                    .cycle 13 3 true (-2),
                    .cycle 16 1 true (0),
                    .cycle 1 18 false (3),
                    .cycle 12 6 false (0),
                    .cycle 1 17 false (3),
                    .cycle 16 1 false (-2),
                    .cycle 13 3 false (-1),
                    .cycle 14 2 true (-2),
                    .cycle 10 17 false (3),
                    .cycle 1 15 false (3),
                    .cycle 11 13 false (1),
                    .cycle 1 19 false (3),
                    .cycle 11 7 false (1),
                    .cycle 16 1 true (0)
                  ]),
            .cycle 11 9 false (1),
            .cycle 12 5 false (0),
            .cycle 1 18 false (3),
            .cycle 15 1 false (-3),
            .cycle 13 2 false (-1),
            .cycle 14 1 false (-2),
            .split 15 (0,true) (byMove [
                    .cycle 0 17 false (3),
                    .cycle 17 1 false (-3),
                    .cycle 13 4 false (-1),
                    .cycle 1 16 false (3),
                    .cycle 12 4 false (0),
                    .last 16 (5,true),
                    .last 30 (5,true),
                    .last 28 (5,true),
                    .cycle 11 14 false (1),
                    .cycle 11 12 false (1),
                    .cycle 13 3 true (-2),
                    .last 32 (5,true),
                    .cycle 11 11 false (1),
                    .cycle 17 1 false (-3),
                    .cycle 13 4 false (-1),
                    .cycle 1 18 false (3),
                    .cycle 12 4 false (0),
                    .last 16 (5,true),
                    .cycle 10 18 false (3),
                    .cycle 10 16 false (2),
                    .cycle 2 14 false (3),
                    .cycle 10 20 false (2),
                    .last 17 (5,true),
                    .cycle 10 20 false (4)
                  ]),
            .cycle 1 16 false (3),
            .cycle 12 4 false (0),
            .cycle 10 16 false (2),
            .cycle 11 4 false (1),
            .split 15 (5,true) (byMove [
                    .last 16 (0,true),
                    .cycle 17 1 false (-3),
                    .cycle 13 4 false (-1),
                    .cycle 1 16 false (3),
                    .cycle 12 4 false (0),
                    .cycle 17 1 true (-3),
                    .last 31 (0,true),
                    .cycle 30 1 false (-2),
                    .cycle 11 14 false (1),
                    .cycle 11 12 false (1),
                    .cycle 13 3 true (-2),
                    .cycle 16 1 true (0),
                    .last 16 (0,true),
                    .cycle 17 1 false (-3),
                    .cycle 13 4 false (-1),
                    .cycle 1 18 false (3),
                    .cycle 12 4 false (0),
                    .cycle 14 3 false (-1),
                    .cycle 10 18 false (3),
                    .cycle 10 16 false (2),
                    .cycle 2 14 false (3),
                    .cycle 10 20 false (2),
                    .cycle 10 8 false (2),
                    .cycle 16 1 true (0)
                  ])
          ]),
      .cycle 10 15 false (3),
      .cycle 1 13 false (3),
      .cycle 11 11 false (1),
      .cycle 1 17 false (3),
      .cycle 13 1 true (-1),
      .split 14 (5,false) (byMove [
            .split 15 (0,true) (byMove [
                    .cycle 0 16 false (3),
                    .cycle 11 14 false (1),
                    .cycle 17 1 false (-1),
                    .cycle 16 1 false (-2),
                    .cycle 13 3 false (0),
                    .cycle 0 17 false (3),
                    .cycle 0 16 true (-1),
                    .cycle 11 14 true (-1),
                    .cycle 17 1 false (1),
                    .cycle 16 1 false (0),
                    .cycle 13 3 true (-1),
                    .cycle 0 17 false (3),
                    .cycle 1 18 false (3),
                    .cycle 12 6 false (0),
                    .cycle 1 17 false (3),
                    .cycle 16 1 false (-2),
                    .last 17 (5,true),
                    .cycle 11 9 false (1),
                    .cycle 10 17 false (3),
                    .cycle 1 15 false (3),
                    .cycle 11 13 false (1),
                    .cycle 1 19 false (3),
                    .cycle 13 3 true (-1),
                    .cycle 14 2 true (-1)
                  ]),
            .cycle 16 1 false (-2),
            .cycle 13 3 false (0),
            .cycle 1 15 false (3),
            .cycle 12 3 false (0),
            .split 15 (5,true) (byMove [
                    .cycle 0 16 false (3),
                    .cycle 11 14 false (1),
                    .cycle 17 1 false (-1),
                    .cycle 16 1 false (-2),
                    .cycle 13 3 false (0),
                    .cycle 16 1 false (-2),
                    .cycle 0 16 true (-1),
                    .cycle 11 14 true (-1),
                    .cycle 17 1 false (1),
                    .cycle 16 1 false (0),
                    .cycle 13 3 true (-1),
                    .cycle 16 1 false (0),
                    .cycle 1 18 false (3),
                    .cycle 12 6 false (0),
                    .cycle 1 17 false (3),
                    .cycle 16 1 false (-2),
                    .cycle 12 6 false (0),
                    .cycle 16 1 false (-2),
                    .cycle 10 17 false (3),
                    .cycle 1 15 false (3),
                    .cycle 11 13 false (1),
                    .cycle 1 19 false (3),
                    .cycle 13 3 true (-1),
                    .cycle 14 2 true (-1)
                  ]),
            .cycle 0 15 true (-1),
            .cycle 11 13 true (-1),
            .cycle 11 13 false (2),
            .cycle 11 11 false (1),
            .cycle 13 2 true (-1),
            .cycle 14 1 true (0),
            .split 15 (0,true) (byMove [
                    .cycle 11 8 false (1),
                    .cycle 35 1 false (-3),
                    .cycle 17 1 false (-1),
                    .cycle 16 1 false (-2),
                    .cycle 13 3 false (0),
                    .last 38 (5,true),
                    .cycle 0 17 true (-1),
                    .cycle 17 1 false (-1),
                    .cycle 13 4 true (-1),
                    .cycle 1 16 true (-1),
                    .cycle 12 4 true (-1),
                    .last 16 (5,true),
                    .cycle 11 10 false (1),
                    .cycle 12 6 false (0),
                    .cycle 1 19 false (3),
                    .cycle 16 1 false (-2),
                    .last 17 (5,true),
                    .cycle 11 11 false (1),
                    .cycle 10 19 false (4),
                    .cycle 1 17 false (3),
                    .cycle 12 5 false (0),
                    .cycle 10 17 false (3),
                    .cycle 11 5 false (1),
                    .last 16 (5,true)
                  ]),
            .cycle 16 1 false (-2),
            .cycle 13 3 false (0),
            .cycle 1 17 false (3),
            .cycle 12 3 false (0),
            .split 15 (5,true) (byMove [
                    .cycle 11 8 false (1),
                    .cycle 35 1 false (-3),
                    .cycle 17 1 false (-1),
                    .cycle 16 1 false (-2),
                    .cycle 13 3 false (0),
                    .cycle 16 1 false (-2),
                    .last 16 (0,true),
                    .cycle 17 1 false (-1),
                    .cycle 13 4 true (-1),
                    .cycle 1 16 true (-1),
                    .cycle 12 4 true (-1),
                    .cycle 17 1 false (1),
                    .cycle 11 10 false (1),
                    .cycle 12 6 false (0),
                    .cycle 1 19 false (3),
                    .cycle 16 1 false (-2),
                    .cycle 12 6 false (0),
                    .cycle 16 1 false (-2),
                    .last 16 (0,true),
                    .cycle 1 17 false (3),
                    .cycle 12 5 false (0),
                    .cycle 10 17 false (3),
                    .cycle 11 5 false (1),
                    .cycle 14 3 true (-1)
                  ]),
            .cycle 10 17 false (4),
            .cycle 10 15 false (3),
            .cycle 2 13 false (3),
            .cycle 10 19 false (3),
            .cycle 13 2 true (-1),
            .cycle 14 1 true (0)
          ])
    ])

theorem checked : zipCheck 44 parent tree = true := by decide +kernel
noncomputable def certificate : WeightedTNFCertificate 44 parent 6 :=
  certifiedZip 44 parent tree parent_root parent_nohalt checked
theorem all_completions_weighted : ∀ m, compatible parent m → WeightedBound 44 m :=
  certificate.sound
theorem cover : Cover (WeightedBound 44) parent := Cover.leaf _ all_completions_weighted

#print axioms ngram_never
#print axioms checked
#print axioms all_completions_weighted
#print axioms cover
end BB6.Agent24Raw45Depth3Full4
