import FastSectionDef
import GenericSection

namespace BB6.Agent11
open BB6.Agent46

/-- The exact original Machine C section orbit has counterexamples to each
    of three broad mod-eight exclusions complementary to the M8 (7,4)
    obstruction. These are finite positive examples, not a C decision. -/
private theorem orbit_0 :
    BB6.Agent8Section.run secNext 0 (some (5,1)) = some (5,1) := rfl

private theorem orbit_1 :
    BB6.Agent8Section.run secNext 1 (some (5,1)) = some (3,4) := by
  change (BB6.Agent8Section.run secNext 0 (some (5,1))).bind secNext = some (3,4)
  rw [orbit_0]
  simp [secNext, exactSection, bounce]

private theorem orbit_2 :
    BB6.Agent8Section.run secNext 2 (some (5,1)) = some (4,7) := by
  change (BB6.Agent8Section.run secNext 1 (some (5,1))).bind secNext = some (4,7)
  rw [orbit_1]
  simp [secNext, exactSection, bounce]

private theorem orbit_3 :
    BB6.Agent8Section.run secNext 3 (some (5,1)) = some (20,4) := by
  change (BB6.Agent8Section.run secNext 2 (some (5,1))).bind secNext = some (20,4)
  rw [orbit_2]
  simp [secNext, exactSection, bounce]

private theorem orbit_4 :
    BB6.Agent8Section.run secNext 4 (some (5,1)) = some (12,10) := by
  change (BB6.Agent8Section.run secNext 3 (some (5,1))).bind secNext = some (12,10)
  rw [orbit_3]
  simp [secNext, exactSection, bounce]

private theorem orbit_5 :
    BB6.Agent8Section.run secNext 5 (some (5,1)) = some (17,11) := by
  change (BB6.Agent8Section.run secNext 4 (some (5,1))).bind secNext = some (17,11)
  rw [orbit_4]
  simp [secNext, exactSection, bounce]

private theorem orbit_6 :
    BB6.Agent8Section.run secNext 6 (some (5,1)) = some (32,7) := by
  change (BB6.Agent8Section.run secNext 5 (some (5,1))).bind secNext = some (32,7)
  rw [orbit_5]
  simp [secNext, exactSection, bounce]

private theorem orbit_7 :
    BB6.Agent8Section.run secNext 7 (some (5,1)) = some (18,16) := by
  change (BB6.Agent8Section.run secNext 6 (some (5,1))).bind secNext = some (18,16)
  rw [orbit_6]
  simp [secNext, exactSection, bounce]

private theorem orbit_8 :
    BB6.Agent8Section.run secNext 8 (some (5,1)) = some (23,17) := by
  change (BB6.Agent8Section.run secNext 7 (some (5,1))).bind secNext = some (23,17)
  rw [orbit_7]
  simp [secNext, exactSection, bounce]

private theorem orbit_9 :
    BB6.Agent8Section.run secNext 9 (some (5,1)) = some (38,13) := by
  change (BB6.Agent8Section.run secNext 8 (some (5,1))).bind secNext = some (38,13)
  rw [orbit_8]
  simp [secNext, exactSection, bounce]

private theorem orbit_10 :
    BB6.Agent8Section.run secNext 10 (some (5,1)) = some (12,28) := by
  change (BB6.Agent8Section.run secNext 9 (some (5,1))).bind secNext = some (12,28)
  rw [orbit_9]
  simp [secNext, exactSection, bounce]

private theorem orbit_11 :
    BB6.Agent8Section.run secNext 11 (some (5,1)) = some (34,22) := by
  change (BB6.Agent8Section.run secNext 10 (some (5,1))).bind secNext = some (34,22)
  rw [orbit_10]
  simp [secNext, exactSection, bounce]

private theorem orbit_12 :
    BB6.Agent8Section.run secNext 12 (some (5,1)) = some (59,13) := by
  change (BB6.Agent8Section.run secNext 11 (some (5,1))).bind secNext = some (59,13)
  rw [orbit_11]
  simp [secNext, exactSection, bounce]

private theorem orbit_13 :
    BB6.Agent8Section.run secNext 13 (some (5,1)) = some (33,28) := by
  change (BB6.Agent8Section.run secNext 12 (some (5,1))).bind secNext = some (33,28)
  rw [orbit_12]
  simp [secNext, exactSection, bounce]

private theorem orbit_14 :
    BB6.Agent8Section.run secNext 14 (some (5,1)) = some (46,25) := by
  change (BB6.Agent8Section.run secNext 13 (some (5,1))).bind secNext = some (46,25)
  rw [orbit_13]
  simp [secNext, exactSection, bounce]

private theorem orbit_15 :
    BB6.Agent8Section.run secNext 15 (some (5,1)) = some (89,7) := by
  change (BB6.Agent8Section.run secNext 14 (some (5,1))).bind secNext = some (89,7)
  rw [orbit_14]
  simp [secNext, exactSection, bounce]

private theorem orbit_16 :
    BB6.Agent8Section.run secNext 16 (some (5,1)) = some (75,16) := by
  change (BB6.Agent8Section.run secNext 15 (some (5,1))).bind secNext = some (75,16)
  rw [orbit_15]
  simp [secNext, exactSection, bounce]

private theorem orbit_17 :
    BB6.Agent8Section.run secNext 17 (some (5,1)) = some (43,34) := by
  change (BB6.Agent8Section.run secNext 16 (some (5,1))).bind secNext = some (43,34)
  rw [orbit_16]
  simp [secNext, exactSection, bounce]

private theorem orbit_18 :
    BB6.Agent8Section.run secNext 18 (some (5,1)) = some (64,27) := by
  change (BB6.Agent8Section.run secNext 17 (some (5,1))).bind secNext = some (64,27)
  rw [orbit_17]
  simp [secNext, exactSection, bounce]

private theorem orbit_19 :
    BB6.Agent8Section.run secNext 19 (some (5,1)) = some (10,56) := by
  change (BB6.Agent8Section.run secNext 18 (some (5,1))).bind secNext = some (10,56)
  rw [orbit_18]
  simp [secNext, exactSection, bounce]

private theorem orbit_20 :
    BB6.Agent8Section.run secNext 20 (some (5,1)) = some (57,39) := by
  change (BB6.Agent8Section.run secNext 19 (some (5,1))).bind secNext = some (57,39)
  rw [orbit_19]
  simp [secNext, exactSection, bounce]

private theorem orbit_21 :
    BB6.Agent8Section.run secNext 21 (some (5,1)) = some (96,23) := by
  change (BB6.Agent8Section.run secNext 20 (some (5,1))).bind secNext = some (96,23)
  rw [orbit_20]
  simp [secNext, exactSection, bounce]

private theorem orbit_22 :
    BB6.Agent8Section.run secNext 22 (some (5,1)) = some (50,48) := by
  change (BB6.Agent8Section.run secNext 21 (some (5,1))).bind secNext = some (50,48)
  rw [orbit_21]
  simp [secNext, exactSection, bounce]

private theorem orbit_23 :
    BB6.Agent8Section.run secNext 23 (some (5,1)) = some (55,49) := by
  change (BB6.Agent8Section.run secNext 22 (some (5,1))).bind secNext = some (55,49)
  rw [orbit_22]
  simp [secNext, exactSection, bounce]

private theorem orbit_24 :
    BB6.Agent8Section.run secNext 24 (some (5,1)) = some (70,45) := by
  change (BB6.Agent8Section.run secNext 23 (some (5,1))).bind secNext = some (70,45)
  rw [orbit_23]
  simp [secNext, exactSection, bounce]

private theorem orbit_25 :
    BB6.Agent8Section.run secNext 25 (some (5,1)) = some (121,23) := by
  change (BB6.Agent8Section.run secNext 24 (some (5,1))).bind secNext = some (121,23)
  rw [orbit_24]
  simp [secNext, exactSection, bounce]

private theorem orbit_26 :
    BB6.Agent8Section.run secNext 26 (some (5,1)) = some (75,48) := by
  change (BB6.Agent8Section.run secNext 25 (some (5,1))).bind secNext = some (75,48)
  rw [orbit_25]
  simp [secNext, exactSection, bounce]

private theorem orbit_27 :
    BB6.Agent8Section.run secNext 27 (some (5,1)) = some (132,23) := by
  change (BB6.Agent8Section.run secNext 26 (some (5,1))).bind secNext = some (132,23)
  rw [orbit_26]
  simp [secNext, exactSection, bounce]

private theorem orbit_28 :
    BB6.Agent8Section.run secNext 28 (some (5,1)) = some (86,48) := by
  change (BB6.Agent8Section.run secNext 27 (some (5,1))).bind secNext = some (86,48)
  rw [orbit_27]
  simp [secNext, exactSection, bounce]

private theorem orbit_29 :
    BB6.Agent8Section.run secNext 29 (some (5,1)) = some (163,13) := by
  change (BB6.Agent8Section.run secNext 28 (some (5,1))).bind secNext = some (163,13)
  rw [orbit_28]
  simp [secNext, exactSection, bounce]

private theorem orbit_30 :
    BB6.Agent8Section.run secNext 30 (some (5,1)) = some (137,28) := by
  change (BB6.Agent8Section.run secNext 29 (some (5,1))).bind secNext = some (137,28)
  rw [orbit_29]
  simp [secNext, exactSection, bounce]

private theorem orbit_31 :
    BB6.Agent8Section.run secNext 31 (some (5,1)) = some (81,58) := by
  change (BB6.Agent8Section.run secNext 30 (some (5,1))).bind secNext = some (81,58)
  rw [orbit_30]
  simp [secNext, exactSection, bounce]

private theorem orbit_32 :
    BB6.Agent8Section.run secNext 32 (some (5,1)) = some (130,37) := by
  change (BB6.Agent8Section.run secNext 31 (some (5,1))).bind secNext = some (130,37)
  rw [orbit_31]
  simp [secNext, exactSection, bounce]

private theorem orbit_33 :
    BB6.Agent8Section.run secNext 33 (some (5,1)) = some (56,76) := by
  change (BB6.Agent8Section.run secNext 32 (some (5,1))).bind secNext = some (56,76)
  rw [orbit_32]
  simp [secNext, exactSection, bounce]

private theorem orbit_34 :
    BB6.Agent8Section.run secNext 34 (some (5,1)) = some (17,99) := by
  change (BB6.Agent8Section.run secNext 33 (some (5,1))).bind secNext = some (17,99)
  rw [orbit_33]
  simp [secNext, exactSection, bounce]

private theorem orbit_35 :
    BB6.Agent8Section.run secNext 35 (some (5,1)) = some (90,69) := by
  change (BB6.Agent8Section.run secNext 34 (some (5,1))).bind secNext = some (90,69)
  rw [orbit_34]
  simp [secNext, exactSection, bounce]

private theorem orbit_36 :
    BB6.Agent8Section.run secNext 36 (some (5,1)) = some (133,51) := by
  change (BB6.Agent8Section.run secNext 35 (some (5,1))).bind secNext = some (133,51)
  rw [orbit_35]
  simp [secNext, exactSection, bounce]

private theorem orbit_37 :
    BB6.Agent8Section.run secNext 37 (some (5,1)) = some (31,104) := by
  change (BB6.Agent8Section.run secNext 36 (some (5,1))).bind secNext = some (31,104)
  rw [orbit_36]
  simp [secNext, exactSection, bounce]

/-- The authentic blank orbit visits first/right residues (3,4). -/
theorem blank_reaches_residue_3_4 :
    BB6.Agent8Section.run secNext 1 (some (5,1)) = some (3,4) := orbit_1
/-- The authentic blank orbit visits first/right residues (3,0). -/
theorem blank_reaches_residue_3_0 :
    BB6.Agent8Section.run secNext 16 (some (5,1)) = some (75,16) := orbit_16
/-- The authentic blank orbit visits first/right residues (7,0). -/
theorem blank_reaches_residue_7_0 :
    BB6.Agent8Section.run secNext 37 (some (5,1)) = some (31,104) := orbit_37

#print axioms blank_reaches_residue_3_4
#print axioms blank_reaches_residue_3_0
#print axioms blank_reaches_residue_7_0
end BB6.Agent11
