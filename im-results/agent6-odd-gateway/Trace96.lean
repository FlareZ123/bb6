import FiniteTarget42
namespace BB6Agent6

theorem blank_at_42 : runT 42 (2,1) = some (76,3) := by
  exact runT_step 41 (2,1) (35,43) (76,3)
    blank_at_41 (by simp [T,G])

theorem blank_at_43 : runT 43 (2,1) = some (79,1) := by
  exact runT_step 42 (2,1) (76,3) (79,1)
    blank_at_42 (by simp [T,G])

theorem blank_at_44 : runT 44 (2,1) = some (81,0) := by
  exact runT_step 43 (2,1) (79,1) (81,0)
    blank_at_43 (by simp [T,G])

theorem blank_at_45 : runT 45 (2,1) = some (2,82) := by
  exact runT_step 44 (2,1) (81,0) (2,82)
    blank_at_44 (by simp [T,G])

theorem blank_at_46 : runT 46 (2,1) = some (5,80) := by
  exact runT_step 45 (2,1) (2,82) (5,80)
    blank_at_45 (by simp [T,G])

theorem blank_at_47 : runT 47 (2,1) = some (16,70) := by
  exact runT_step 46 (2,1) (5,80) (16,70)
    blank_at_46 (by simp [T,G])

theorem blank_at_48 : runT 48 (2,1) = some (19,68) := by
  exact runT_step 47 (2,1) (16,70) (19,68)
    blank_at_47 (by simp [T,G])

theorem blank_at_49 : runT 49 (2,1) = some (44,44) := by
  exact runT_step 48 (2,1) (19,68) (44,44)
    blank_at_48 (by simp [T,G])

theorem blank_at_50 : runT 50 (2,1) = some (47,42) := by
  exact runT_step 49 (2,1) (44,44) (47,42)
    blank_at_49 (by simp [T,G])

theorem blank_at_51 : runT 51 (2,1) = some (16,75) := by
  exact runT_step 50 (2,1) (47,42) (16,75)
    blank_at_50 (by simp [T,G])

theorem blank_at_52 : runT 52 (2,1) = some (19,73) := by
  exact runT_step 51 (2,1) (16,75) (19,73)
    blank_at_51 (by simp [T,G])

theorem blank_at_53 : runT 53 (2,1) = some (44,49) := by
  exact runT_step 52 (2,1) (19,73) (44,49)
    blank_at_52 (by simp [T,G])

theorem blank_at_54 : runT 54 (2,1) = some (47,47) := by
  exact runT_step 53 (2,1) (44,49) (47,47)
    blank_at_53 (by simp [T,G])

theorem blank_at_55 : runT 55 (2,1) = some (8,89) := by
  exact runT_step 54 (2,1) (47,47) (8,89)
    blank_at_54 (by simp [T,G])

theorem blank_at_56 : runT 56 (2,1) = some (11,87) := by
  exact runT_step 55 (2,1) (8,89) (11,87)
    blank_at_55 (by simp [T,G])

theorem blank_at_57 : runT 57 (2,1) = some (28,71) := by
  exact runT_step 56 (2,1) (11,87) (28,71)
    blank_at_56 (by simp [T,G])

theorem blank_at_58 : runT 58 (2,1) = some (31,69) := by
  exact runT_step 57 (2,1) (28,71) (31,69)
    blank_at_57 (by simp [T,G])

theorem blank_at_59 : runT 59 (2,1) = some (68,33) := by
  exact runT_step 58 (2,1) (31,69) (68,33)
    blank_at_58 (by simp [T,G])

theorem blank_at_60 : runT 60 (2,1) = some (71,31) := by
  exact runT_step 59 (2,1) (68,33) (71,31)
    blank_at_59 (by simp [T,G])

theorem blank_at_61 : runT 61 (2,1) = some (88,17) := by
  exact runT_step 60 (2,1) (71,31) (88,17)
    blank_at_60 (by simp [T,G])

theorem blank_at_62 : runT 62 (2,1) = some (91,15) := by
  exact runT_step 61 (2,1) (88,17) (91,15)
    blank_at_61 (by simp [T,G])

theorem blank_at_63 : runT 63 (2,1) = some (100,11) := by
  exact runT_step 62 (2,1) (91,15) (100,11)
    blank_at_62 (by simp [T,G])

theorem blank_at_64 : runT 64 (2,1) = some (103,9) := by
  exact runT_step 63 (2,1) (100,11) (103,9)
    blank_at_63 (by simp [T,G])

theorem blank_at_65 : runT 65 (2,1) = some (84,35) := by
  exact runT_step 64 (2,1) (103,9) (84,35)
    blank_at_64 (by simp [T,G])

theorem blank_at_66 : runT 66 (2,1) = some (87,33) := by
  exact runT_step 65 (2,1) (84,35) (87,33)
    blank_at_65 (by simp [T,G])

theorem blank_at_67 : runT 67 (2,1) = some (116,7) := by
  exact runT_step 66 (2,1) (87,33) (116,7)
    blank_at_66 (by simp [T,G])

theorem blank_at_68 : runT 68 (2,1) = some (119,5) := by
  exact runT_step 67 (2,1) (116,7) (119,5)
    blank_at_67 (by simp [T,G])

theorem blank_at_69 : runT 69 (2,1) = some (80,53) := by
  exact runT_step 68 (2,1) (119,5) (80,53)
    blank_at_68 (by simp [T,G])

theorem blank_at_70 : runT 70 (2,1) = some (83,51) := by
  exact runT_step 69 (2,1) (80,53) (83,51)
    blank_at_69 (by simp [T,G])

theorem blank_at_71 : runT 71 (2,1) = some (72,65) := by
  exact runT_step 70 (2,1) (83,51) (72,65)
    blank_at_70 (by simp [T,G])

theorem blank_at_72 : runT 72 (2,1) = some (75,63) := by
  exact runT_step 71 (2,1) (72,65) (75,63)
    blank_at_71 (by simp [T,G])

theorem blank_at_73 : runT 73 (2,1) = some (32,109) := by
  exact runT_step 72 (2,1) (75,63) (32,109)
    blank_at_72 (by simp [T,G])

theorem blank_at_74 : runT 74 (2,1) = some (35,107) := by
  exact runT_step 73 (2,1) (32,109) (35,107)
    blank_at_73 (by simp [T,G])

theorem blank_at_75 : runT 75 (2,1) = some (76,67) := by
  exact runT_step 74 (2,1) (35,107) (76,67)
    blank_at_74 (by simp [T,G])

theorem blank_at_76 : runT 76 (2,1) = some (79,65) := by
  exact runT_step 75 (2,1) (76,67) (79,65)
    blank_at_75 (by simp [T,G])

theorem blank_at_77 : runT 77 (2,1) = some (36,111) := by
  exact runT_step 76 (2,1) (79,65) (36,111)
    blank_at_76 (by simp [T,G])

theorem blank_at_78 : runT 78 (2,1) = some (39,109) := by
  exact runT_step 77 (2,1) (36,111) (39,109)
    blank_at_77 (by simp [T,G])

theorem blank_at_79 : runT 79 (2,1) = some (84,65) := by
  exact runT_step 78 (2,1) (39,109) (84,65)
    blank_at_78 (by simp [T,G])

theorem blank_at_80 : runT 80 (2,1) = some (87,63) := by
  exact runT_step 79 (2,1) (84,65) (87,63)
    blank_at_79 (by simp [T,G])

theorem blank_at_81 : runT 81 (2,1) = some (56,97) := by
  exact runT_step 80 (2,1) (87,63) (56,97)
    blank_at_80 (by simp [T,G])

theorem blank_at_82 : runT 82 (2,1) = some (59,95) := by
  exact runT_step 81 (2,1) (56,97) (59,95)
    blank_at_81 (by simp [T,G])

theorem blank_at_83 : runT 83 (2,1) = some (124,31) := by
  exact runT_step 82 (2,1) (59,95) (124,31)
    blank_at_82 (by simp [T,G])

theorem blank_at_84 : runT 84 (2,1) = some (127,29) := by
  exact runT_step 83 (2,1) (124,31) (127,29)
    blank_at_83 (by simp [T,G])

theorem blank_at_85 : runT 85 (2,1) = some (88,73) := by
  exact runT_step 84 (2,1) (127,29) (88,73)
    blank_at_84 (by simp [T,G])

theorem blank_at_86 : runT 86 (2,1) = some (91,71) := by
  exact runT_step 85 (2,1) (88,73) (91,71)
    blank_at_85 (by simp [T,G])

theorem blank_at_87 : runT 87 (2,1) = some (48,117) := by
  exact runT_step 86 (2,1) (91,71) (48,117)
    blank_at_86 (by simp [T,G])

theorem blank_at_88 : runT 88 (2,1) = some (51,115) := by
  exact runT_step 87 (2,1) (48,117) (51,115)
    blank_at_87 (by simp [T,G])

theorem blank_at_89 : runT 89 (2,1) = some (108,59) := by
  exact runT_step 88 (2,1) (51,115) (108,59)
    blank_at_88 (by simp [T,G])

theorem blank_at_90 : runT 90 (2,1) = some (111,57) := by
  exact runT_step 89 (2,1) (108,59) (111,57)
    blank_at_89 (by simp [T,G])

theorem blank_at_91 : runT 91 (2,1) = some (116,55) := by
  exact runT_step 90 (2,1) (111,57) (116,55)
    blank_at_90 (by simp [T,G])

theorem blank_at_92 : runT 92 (2,1) = some (119,53) := by
  exact runT_step 91 (2,1) (116,55) (119,53)
    blank_at_91 (by simp [T,G])

theorem blank_at_93 : runT 93 (2,1) = some (140,35) := by
  exact runT_step 92 (2,1) (119,53) (140,35)
    blank_at_92 (by simp [T,G])

theorem blank_at_94 : runT 94 (2,1) = some (143,33) := by
  exact runT_step 93 (2,1) (140,35) (143,33)
    blank_at_93 (by simp [T,G])

theorem blank_at_95 : runT 95 (2,1) = some (96,85) := by
  exact runT_step 94 (2,1) (143,33) (96,85)
    blank_at_94 (by simp [T,G])

theorem blank_at_96 : runT 96 (2,1) = some (99,83) := by
  exact runT_step 95 (2,1) (96,85) (99,83)
    blank_at_95 (by simp [T,G])

end BB6Agent6
