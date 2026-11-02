import RankBase

namespace BB6.Agent7
open BB6.P1Reduction

theorem trace_0 : iterT 0 (2,1) = some (2,1) := rfl

theorem trace_1 : iterT 1 (2,1) = some (4,0) := by
  rw [show 1 = 0+1 by omega, iterT_add, trace_0]
  change iterT 1 (2,1) = some (4,0)
  rw [← iterFast_correct]
  decide

theorem trace_2 : iterT 2 (2,1) = some (2,5) := by
  rw [show 2 = 1+1 by omega, iterT_add, trace_1]
  change iterT 1 (4,0) = some (2,5)
  rw [← iterFast_correct]
  decide

theorem trace_8 : iterT 8 (2,1) = some (0,17) := by
  rw [show 8 = 2+6 by omega, iterT_add, trace_2]
  change iterT 6 (2,5) = some (0,17)
  rw [← iterFast_correct]
  decide

theorem trace_9 : iterT 9 (2,1) = some (3,15) := by
  rw [show 9 = 8+1 by omega, iterT_add, trace_8]
  change iterT 1 (0,17) = some (3,15)
  rw [← iterFast_correct]
  decide

theorem trace_10 : iterT 10 (2,1) = some (12,7) := by
  rw [show 10 = 9+1 by omega, iterT_add, trace_9]
  change iterT 1 (3,15) = some (12,7)
  rw [← iterFast_correct]
  decide

theorem trace_20 : iterT 20 (2,1) = some (20,17) := by
  rw [show 20 = 10+10 by omega, iterT_add, trace_10]
  change iterT 10 (12,7) = some (20,17)
  rw [← iterFast_correct]
  decide

theorem trace_23 : iterT 23 (2,1) = some (27,15) := by
  rw [show 23 = 20+3 by omega, iterT_add, trace_20]
  change iterT 3 (20,17) = some (27,15)
  rw [← iterFast_correct]
  decide

theorem trace_24 : iterT 24 (2,1) = some (32,13) := by
  rw [show 24 = 23+1 by omega, iterT_add, trace_23]
  change iterT 1 (27,15) = some (32,13)
  rw [← iterFast_correct]
  decide

theorem trace_30 : iterT 30 (2,1) = some (56,1) := by
  rw [show 30 = 24+6 by omega, iterT_add, trace_24]
  change iterT 6 (32,13) = some (56,1)
  rw [← iterFast_correct]
  decide

theorem trace_40 : iterT 40 (2,1) = some (32,45) := by
  rw [show 40 = 30+10 by omega, iterT_add, trace_30]
  change iterT 10 (56,1) = some (32,45)
  rw [← iterFast_correct]
  decide

theorem trace_50 : iterT 50 (2,1) = some (47,42) := by
  rw [show 50 = 40+10 by omega, iterT_add, trace_40]
  change iterT 10 (32,45) = some (47,42)
  rw [← iterFast_correct]
  decide

theorem trace_55 : iterT 55 (2,1) = some (8,89) := by
  rw [show 55 = 50+5 by omega, iterT_add, trace_50]
  change iterT 5 (47,42) = some (8,89)
  rw [← iterFast_correct]
  decide

theorem trace_56 : iterT 56 (2,1) = some (11,87) := by
  rw [show 56 = 55+1 by omega, iterT_add, trace_55]
  change iterT 1 (8,89) = some (11,87)
  rw [← iterFast_correct]
  decide

theorem trace_60 : iterT 60 (2,1) = some (71,31) := by
  rw [show 60 = 56+4 by omega, iterT_add, trace_56]
  change iterT 4 (11,87) = some (71,31)
  rw [← iterFast_correct]
  decide

theorem trace_70 : iterT 70 (2,1) = some (83,51) := by
  rw [show 70 = 60+10 by omega, iterT_add, trace_60]
  change iterT 10 (71,31) = some (83,51)
  rw [← iterFast_correct]
  decide

theorem trace_80 : iterT 80 (2,1) = some (87,63) := by
  rw [show 80 = 70+10 by omega, iterT_add, trace_70]
  change iterT 10 (83,51) = some (87,63)
  rw [← iterFast_correct]
  decide

theorem trace_90 : iterT 90 (2,1) = some (111,57) := by
  rw [show 90 = 80+10 by omega, iterT_add, trace_80]
  change iterT 10 (87,63) = some (111,57)
  rw [← iterFast_correct]
  decide

theorem trace_100 : iterT 100 (2,1) = some (95,93) := by
  rw [show 100 = 90+10 by omega, iterT_add, trace_90]
  change iterT 10 (111,57) = some (95,93)
  rw [← iterFast_correct]
  decide

theorem trace_110 : iterT 110 (2,1) = some (163,43) := by
  rw [show 110 = 100+10 by omega, iterT_add, trace_100]
  change iterT 10 (95,93) = some (163,43)
  rw [← iterFast_correct]
  decide

theorem trace_111 : iterT 111 (2,1) = some (76,135) := by
  rw [show 111 = 110+1 by omega, iterT_add, trace_110]
  change iterT 1 (163,43) = some (76,135)
  rw [← iterFast_correct]
  decide

theorem trace_120 : iterT 120 (2,1) = some (107,119) := by
  rw [show 120 = 111+9 by omega, iterT_add, trace_111]
  change iterT 9 (76,135) = some (107,119)
  rw [← iterFast_correct]
  decide

theorem trace_130 : iterT 130 (2,1) = some (127,125) := by
  rw [show 130 = 120+10 by omega, iterT_add, trace_120]
  change iterT 10 (107,119) = some (127,125)
  rw [← iterFast_correct]
  decide

theorem trace_140 : iterT 140 (2,1) = some (219,47) := by
  rw [show 140 = 130+10 by omega, iterT_add, trace_130]
  change iterT 10 (127,125) = some (219,47)
  rw [← iterFast_correct]
  decide

theorem trace_150 : iterT 150 (2,1) = some (19,265) := by
  rw [show 150 = 140+10 by omega, iterT_add, trace_140]
  change iterT 10 (219,47) = some (19,265)
  rw [← iterFast_correct]
  decide

theorem trace_160 : iterT 160 (2,1) = some (107,199) := by
  rw [show 160 = 150+10 by omega, iterT_add, trace_150]
  change iterT 10 (19,265) = some (107,199)
  rw [← iterFast_correct]
  decide

theorem trace_170 : iterT 170 (2,1) = some (191,141) := by
  rw [show 170 = 160+10 by omega, iterT_add, trace_160]
  change iterT 10 (107,199) = some (191,141)
  rw [← iterFast_correct]
  decide

theorem trace_180 : iterT 180 (2,1) = some (71,279) := by
  rw [show 180 = 170+10 by omega, iterT_add, trace_170]
  change iterT 10 (191,141) = some (71,279)
  rw [← iterFast_correct]
  decide

theorem trace_190 : iterT 190 (2,1) = some (135,231) := by
  rw [show 190 = 180+10 by omega, iterT_add, trace_180]
  change iterT 10 (71,279) = some (135,231)
  rw [← iterFast_correct]
  decide

theorem trace_200 : iterT 200 (2,1) = some (343,37) := by
  rw [show 200 = 190+10 by omega, iterT_add, trace_190]
  change iterT 10 (135,231) = some (343,37)
  rw [← iterFast_correct]
  decide

theorem trace_210 : iterT 210 (2,1) = some (63,349) := by
  rw [show 210 = 200+10 by omega, iterT_add, trace_200]
  change iterT 10 (343,37) = some (63,349)
  rw [← iterFast_correct]
  decide

theorem trace_219 : iterT 219 (2,1) = some (272,157) := by
  rw [show 219 = 210+9 by omega, iterT_add, trace_210]
  change iterT 9 (63,349) = some (272,157)
  rw [← iterFast_correct]
  decide

theorem trace_220 : iterT 220 (2,1) = some (275,155) := by
  rw [show 220 = 219+1 by omega, iterT_add, trace_219]
  change iterT 1 (272,157) = some (275,155)
  rw [← iterFast_correct]
  decide

theorem trace_230 : iterT 230 (2,1) = some (91,359) := by
  rw [show 230 = 220+10 by omega, iterT_add, trace_220]
  change iterT 10 (275,155) = some (91,359)
  rw [← iterFast_correct]
  decide

theorem trace_240 : iterT 240 (2,1) = some (423,47) := by
  rw [show 240 = 230+10 by omega, iterT_add, trace_230]
  change iterT 10 (91,359) = some (423,47)
  rw [← iterFast_correct]
  decide

theorem trace_250 : iterT 250 (2,1) = some (355,139) := by
  rw [show 250 = 240+10 by omega, iterT_add, trace_240]
  change iterT 10 (423,47) = some (355,139)
  rw [← iterFast_correct]
  decide

theorem trace_260 : iterT 260 (2,1) = some (39,475) := by
  rw [show 260 = 250+10 by omega, iterT_add, trace_250]
  change iterT 10 (355,139) = some (39,475)
  rw [← iterFast_correct]
  decide

theorem trace_270 : iterT 270 (2,1) = some (207,325) := by
  rw [show 270 = 260+10 by omega, iterT_add, trace_260]
  change iterT 10 (39,475) = some (207,325)
  rw [← iterFast_correct]
  decide

theorem trace_280 : iterT 280 (2,1) = some (219,335) := by
  rw [show 280 = 270+10 by omega, iterT_add, trace_270]
  change iterT 10 (207,325) = some (219,335)
  rw [← iterFast_correct]
  decide

theorem trace_290 : iterT 290 (2,1) = some (15,561) := by
  rw [show 290 = 280+10 by omega, iterT_add, trace_280]
  change iterT 10 (219,335) = some (15,561)
  rw [← iterFast_correct]
  decide

theorem trace_300 : iterT 300 (2,1) = some (343,245) := by
  rw [show 300 = 290+10 by omega, iterT_add, trace_290]
  change iterT 10 (15,561) = some (343,245)
  rw [← iterFast_correct]
  decide

theorem trace_310 : iterT 310 (2,1) = some (239,373) := by
  rw [show 310 = 300+10 by omega, iterT_add, trace_300]
  change iterT 10 (343,245) = some (239,373)
  rw [← iterFast_correct]
  decide

theorem trace_320 : iterT 320 (2,1) = some (634,0) := by
  rw [show 320 = 310+10 by omega, iterT_add, trace_310]
  change iterT 10 (239,373) = some (634,0)
  rw [← iterFast_correct]
  decide

theorem trace_330 : iterT 330 (2,1) = some (215,431) := by
  rw [show 330 = 320+10 by omega, iterT_add, trace_320]
  change iterT 10 (634,0) = some (215,431)
  rw [← iterFast_correct]
  decide

theorem trace_340 : iterT 340 (2,1) = some (567,99) := by
  rw [show 340 = 330+10 by omega, iterT_add, trace_330]
  change iterT 10 (215,431) = some (567,99)
  rw [← iterFast_correct]
  decide

theorem trace_350 : iterT 350 (2,1) = some (303,385) := by
  rw [show 350 = 340+10 by omega, iterT_add, trace_340]
  change iterT 10 (567,99) = some (303,385)
  rw [← iterFast_correct]
  decide

theorem trace_360 : iterT 360 (2,1) = some (295,411) := by
  rw [show 360 = 350+10 by omega, iterT_add, trace_350]
  change iterT 10 (303,385) = some (295,411)
  rw [← iterFast_correct]
  decide

theorem trace_370 : iterT 370 (2,1) = some (695,29) := by
  rw [show 370 = 360+10 by omega, iterT_add, trace_360]
  change iterT 10 (295,411) = some (695,29)
  rw [← iterFast_correct]
  decide

theorem trace_380 : iterT 380 (2,1) = some (311,439) := by
  rw [show 380 = 370+10 by omega, iterT_add, trace_370]
  change iterT 10 (695,29) = some (311,439)
  rw [← iterFast_correct]
  decide

theorem trace_390 : iterT 390 (2,1) = some (543,229) := by
  rw [show 390 = 380+10 by omega, iterT_add, trace_380]
  change iterT 10 (311,439) = some (543,229)
  rw [← iterFast_correct]
  decide

theorem trace_400 : iterT 400 (2,1) = some (395,399) := by
  rw [show 400 = 390+10 by omega, iterT_add, trace_390]
  change iterT 10 (543,229) = some (395,399)
  rw [← iterFast_correct]
  decide

theorem trace_410 : iterT 410 (2,1) = some (183,623) := by
  rw [show 410 = 400+10 by omega, iterT_add, trace_400]
  change iterT 10 (395,399) = some (183,623)
  rw [← iterFast_correct]
  decide

theorem trace_420 : iterT 420 (2,1) = some (195,643) := by
  rw [show 420 = 410+10 by omega, iterT_add, trace_410]
  change iterT 10 (183,623) = some (195,643)
  rw [← iterFast_correct]
  decide

theorem trace_430 : iterT 430 (2,1) = some (471,389) := by
  rw [show 430 = 420+10 by omega, iterT_add, trace_420]
  change iterT 10 (195,643) = some (471,389)
  rw [← iterFast_correct]
  decide

theorem trace_438 : iterT 438 (2,1) = some (619,255) := by
  rw [show 438 = 430+8 by omega, iterT_add, trace_430]
  change iterT 8 (471,389) = some (619,255)
  rw [← iterFast_correct]
  decide

theorem trace_439 : iterT 439 (2,1) = some (736,141) := by
  rw [show 439 = 438+1 by omega, iterT_add, trace_438]
  change iterT 1 (619,255) = some (736,141)
  rw [← iterFast_correct]
  decide

theorem trace_440 : iterT 440 (2,1) = some (739,139) := by
  rw [show 440 = 439+1 by omega, iterT_add, trace_439]
  change iterT 1 (736,141) = some (739,139)
  rw [← iterFast_correct]
  decide

theorem trace_450 : iterT 450 (2,1) = some (599,305) := by
  rw [show 450 = 440+10 by omega, iterT_add, trace_440]
  change iterT 10 (739,139) = some (599,305)
  rw [← iterFast_correct]
  decide

theorem trace_460 : iterT 460 (2,1) = some (775,147) := by
  rw [show 460 = 450+10 by omega, iterT_add, trace_450]
  change iterT 10 (599,305) = some (775,147)
  rw [← iterFast_correct]
  decide

theorem trace_470 : iterT 470 (2,1) = some (879,73) := by
  rw [show 470 = 460+10 by omega, iterT_add, trace_460]
  change iterT 10 (775,147) = some (879,73)
  rw [← iterFast_correct]
  decide

theorem trace_480 : iterT 480 (2,1) = some (647,329) := by
  rw [show 480 = 470+10 by omega, iterT_add, trace_470]
  change iterT 10 (879,73) = some (647,329)
  rw [← iterFast_correct]
  decide

theorem trace_490 : iterT 490 (2,1) = some (871,123) := by
  rw [show 490 = 480+10 by omega, iterT_add, trace_480]
  change iterT 10 (647,329) = some (871,123)
  rw [← iterFast_correct]
  decide

theorem trace_500 : iterT 500 (2,1) = some (567,443) := by
  rw [show 500 = 490+10 by omega, iterT_add, trace_490]
  change iterT 10 (871,123) = some (567,443)
  rw [← iterFast_correct]
  decide

theorem trace_510 : iterT 510 (2,1) = some (375,649) := by
  rw [show 510 = 500+10 by omega, iterT_add, trace_500]
  change iterT 10 (567,443) = some (375,649)
  rw [← iterFast_correct]
  decide

theorem trace_520 : iterT 520 (2,1) = some (823,227) := by
  rw [show 520 = 510+10 by omega, iterT_add, trace_510]
  change iterT 10 (375,649) = some (823,227)
  rw [← iterFast_correct]
  decide

theorem trace_530 : iterT 530 (2,1) = some (247,821) := by
  rw [show 530 = 520+10 by omega, iterT_add, trace_520]
  change iterT 10 (823,227) = some (247,821)
  rw [← iterFast_correct]
  decide

theorem trace_540 : iterT 540 (2,1) = some (399,689) := by
  rw [show 540 = 530+10 by omega, iterT_add, trace_530]
  change iterT 10 (247,821) = some (399,689)
  rw [← iterFast_correct]
  decide

theorem trace_550 : iterT 550 (2,1) = some (455,665) := by
  rw [show 550 = 540+10 by omega, iterT_add, trace_540]
  change iterT 10 (399,689) = some (455,665)
  rw [← iterFast_correct]
  decide

theorem trace_560 : iterT 560 (2,1) = some (11,1127) := by
  rw [show 560 = 550+10 by omega, iterT_add, trace_550]
  change iterT 10 (455,665) = some (11,1127)
  rw [← iterFast_correct]
  decide

theorem trace_570 : iterT 570 (2,1) = some (631,517) := by
  rw [show 570 = 560+10 by omega, iterT_add, trace_560]
  change iterT 10 (11,1127) = some (631,517)
  rw [← iterFast_correct]
  decide

theorem trace_580 : iterT 580 (2,1) = some (551,617) := by
  rw [show 580 = 570+10 by omega, iterT_add, trace_570]
  change iterT 10 (631,517) = some (551,617)
  rw [← iterFast_correct]
  decide

theorem trace_590 : iterT 590 (2,1) = some (295,895) := by
  rw [show 590 = 580+10 by omega, iterT_add, trace_580]
  change iterT 10 (551,617) = some (295,895)
  rw [← iterFast_correct]
  decide

theorem trace_600 : iterT 600 (2,1) = some (247,955) := by
  rw [show 600 = 590+10 by omega, iterT_add, trace_590]
  change iterT 10 (295,895) = some (247,955)
  rw [← iterFast_correct]
  decide

theorem trace_610 : iterT 610 (2,1) = some (859,367) := by
  rw [show 610 = 600+10 by omega, iterT_add, trace_600]
  change iterT 10 (247,955) = some (859,367)
  rw [← iterFast_correct]
  decide

theorem trace_620 : iterT 620 (2,1) = some (259,995) := by
  rw [show 620 = 610+10 by omega, iterT_add, trace_610]
  change iterT 10 (859,367) = some (259,995)
  rw [← iterFast_correct]
  decide

theorem trace_630 : iterT 630 (2,1) = some (335,937) := by
  rw [show 630 = 620+10 by omega, iterT_add, trace_620]
  change iterT 10 (259,995) = some (335,937)
  rw [← iterFast_correct]
  decide

theorem trace_640 : iterT 640 (2,1) = some (419,867) := by
  rw [show 640 = 630+10 by omega, iterT_add, trace_630]
  change iterT 10 (335,937) = some (419,867)
  rw [← iterFast_correct]
  decide

theorem trace_650 : iterT 650 (2,1) = some (599,703) := by
  rw [show 650 = 640+10 by omega, iterT_add, trace_640]
  change iterT 10 (419,867) = some (599,703)
  rw [← iterFast_correct]
  decide

theorem trace_660 : iterT 660 (2,1) = some (1007,325) := by
  rw [show 660 = 650+10 by omega, iterT_add, trace_650]
  change iterT 10 (599,703) = some (1007,325)
  rw [← iterFast_correct]
  decide

theorem trace_670 : iterT 670 (2,1) = some (1335,11) := by
  rw [show 670 = 660+10 by omega, iterT_add, trace_660]
  change iterT 10 (1007,325) = some (1335,11)
  rw [← iterFast_correct]
  decide

theorem trace_680 : iterT 680 (2,1) = some (247,1127) := by
  rw [show 680 = 670+10 by omega, iterT_add, trace_670]
  change iterT 10 (1335,11) = some (247,1127)
  rw [← iterFast_correct]
  decide

theorem trace_690 : iterT 690 (2,1) = some (1239,155) := by
  rw [show 690 = 680+10 by omega, iterT_add, trace_680]
  change iterT 10 (247,1127) = some (1239,155)
  rw [← iterFast_correct]
  decide

theorem trace_700 : iterT 700 (2,1) = some (843,575) := by
  rw [show 700 = 690+10 by omega, iterT_add, trace_690]
  change iterT 10 (1239,155) = some (843,575)
  rw [← iterFast_correct]
  decide

theorem trace_710 : iterT 710 (2,1) = some (1191,243) := by
  rw [show 710 = 700+10 by omega, iterT_add, trace_700]
  change iterT 10 (843,575) = some (1191,243)
  rw [← iterFast_correct]
  decide

theorem trace_720 : iterT 720 (2,1) = some (1095,361) := by
  rw [show 720 = 710+10 by omega, iterT_add, trace_710]
  change iterT 10 (1191,243) = some (1095,361)
  rw [← iterFast_correct]
  decide

theorem trace_730 : iterT 730 (2,1) = some (695,775) := by
  rw [show 730 = 720+10 by omega, iterT_add, trace_720]
  change iterT 10 (1095,361) = some (695,775)
  rw [← iterFast_correct]
  decide

theorem trace_740 : iterT 740 (2,1) = some (339,1155) := by
  rw [show 740 = 730+10 by omega, iterT_add, trace_730]
  change iterT 10 (695,775) = some (339,1155)
  rw [← iterFast_correct]
  decide

theorem trace_750 : iterT 750 (2,1) = some (567,947) := by
  rw [show 750 = 740+10 by omega, iterT_add, trace_740]
  change iterT 10 (339,1155) = some (567,947)
  rw [← iterFast_correct]
  decide

theorem trace_760 : iterT 760 (2,1) = some (535,993) := by
  rw [show 760 = 750+10 by omega, iterT_add, trace_750]
  change iterT 10 (567,947) = some (535,993)
  rw [← iterFast_correct]
  decide

theorem trace_770 : iterT 770 (2,1) = some (1415,131) := by
  rw [show 770 = 760+10 by omega, iterT_add, trace_760]
  change iterT 10 (535,993) = some (1415,131)
  rw [← iterFast_correct]
  decide

theorem trace_780 : iterT 780 (2,1) = some (1359,209) := by
  rw [show 780 = 770+10 by omega, iterT_add, trace_770]
  change iterT 10 (1415,131) = some (1359,209)
  rw [← iterFast_correct]
  decide

theorem trace_790 : iterT 790 (2,1) = some (551,1051) := by
  rw [show 790 = 780+10 by omega, iterT_add, trace_780]
  change iterT 10 (1359,209) = some (551,1051)
  rw [← iterFast_correct]
  decide

theorem trace_800 : iterT 800 (2,1) = some (1383,235) := by
  rw [show 800 = 790+10 by omega, iterT_add, trace_790]
  change iterT 10 (551,1051) = some (1383,235)
  rw [← iterFast_correct]
  decide

theorem trace_810 : iterT 810 (2,1) = some (687,961) := by
  rw [show 810 = 800+10 by omega, iterT_add, trace_800]
  change iterT 10 (1383,235) = some (687,961)
  rw [← iterFast_correct]
  decide

theorem trace_820 : iterT 820 (2,1) = some (1651,19) := by
  rw [show 820 = 810+10 by omega, iterT_add, trace_810]
  change iterT 10 (687,961) = some (1651,19)
  rw [← iterFast_correct]
  decide

theorem trace_830 : iterT 830 (2,1) = some (1351,351) := by
  rw [show 830 = 820+10 by omega, iterT_add, trace_820]
  change iterT 10 (1651,19) = some (1351,351)
  rw [← iterFast_correct]
  decide

theorem trace_840 : iterT 840 (2,1) = some (1383,345) := by
  rw [show 840 = 830+10 by omega, iterT_add, trace_830]
  change iterT 10 (1351,351) = some (1383,345)
  rw [← iterFast_correct]
  decide

theorem trace_850 : iterT 850 (2,1) = some (895,853) := by
  rw [show 850 = 840+10 by omega, iterT_add, trace_840]
  change iterT 10 (1383,345) = some (895,853)
  rw [← iterFast_correct]
  decide

theorem trace_860 : iterT 860 (2,1) = some (1655,105) := by
  rw [show 860 = 850+10 by omega, iterT_add, trace_850]
  change iterT 10 (895,853) = some (1655,105)
  rw [← iterFast_correct]
  decide

theorem trace_861 : iterT 861 (2,1) = some (152,1617) := by
  rw [show 861 = 860+1 by omega, iterT_add, trace_860]
  change iterT 1 (1655,105) = some (152,1617)
  rw [← iterFast_correct]
  decide

theorem trace_862 : iterT 862 (2,1) = some (155,1615) := by
  rw [show 862 = 861+1 by omega, iterT_add, trace_861]
  change iterT 1 (152,1617) = some (155,1615)
  rw [← iterFast_correct]
  decide

theorem trace_870 : iterT 870 (2,1) = some (1671,109) := by
  rw [show 870 = 862+8 by omega, iterT_add, trace_862]
  change iterT 8 (155,1615) = some (1671,109)
  rw [← iterFast_correct]
  decide

theorem trace_880 : iterT 880 (2,1) = some (1207,591) := by
  rw [show 880 = 870+10 by omega, iterT_add, trace_870]
  change iterT 10 (1671,109) = some (1207,591)
  rw [← iterFast_correct]
  decide

theorem trace_890 : iterT 890 (2,1) = some (855,961) := by
  rw [show 890 = 880+10 by omega, iterT_add, trace_880]
  change iterT 10 (1207,591) = some (855,961)
  rw [← iterFast_correct]
  decide

theorem trace_900 : iterT 900 (2,1) = some (191,1645) := by
  rw [show 900 = 890+10 by omega, iterT_add, trace_890]
  change iterT 10 (855,961) = some (191,1645)
  rw [← iterFast_correct]
  decide

theorem trace_910 : iterT 910 (2,1) = some (1127,729) := by
  rw [show 910 = 900+10 by omega, iterT_add, trace_900]
  change iterT 10 (191,1645) = some (1127,729)
  rw [← iterFast_correct]
  decide

theorem trace_920 : iterT 920 (2,1) = some (1655,227) := by
  rw [show 920 = 910+10 by omega, iterT_add, trace_910]
  change iterT 10 (1127,729) = some (1655,227)
  rw [← iterFast_correct]
  decide

theorem trace_930 : iterT 930 (2,1) = some (919,981) := by
  rw [show 930 = 920+10 by omega, iterT_add, trace_920]
  change iterT 10 (1655,227) = some (919,981)
  rw [← iterFast_correct]
  decide

theorem trace_940 : iterT 940 (2,1) = some (299,1623) := by
  rw [show 940 = 930+10 by omega, iterT_add, trace_930]
  change iterT 10 (919,981) = some (299,1623)
  rw [← iterFast_correct]
  decide

theorem trace_950 : iterT 950 (2,1) = some (719,1217) := by
  rw [show 950 = 940+10 by omega, iterT_add, trace_940]
  change iterT 10 (299,1623) = some (719,1217)
  rw [← iterFast_correct]
  decide

theorem trace_960 : iterT 960 (2,1) = some (531,1435) := by
  rw [show 960 = 950+10 by omega, iterT_add, trace_950]
  change iterT 10 (719,1217) = some (531,1435)
  rw [← iterFast_correct]
  decide

theorem trace_970 : iterT 970 (2,1) = some (1911,69) := by
  rw [show 970 = 960+10 by omega, iterT_add, trace_960]
  change iterT 10 (531,1435) = some (1911,69)
  rw [← iterFast_correct]
  decide

theorem trace_980 : iterT 980 (2,1) = some (855,1149) := by
  rw [show 980 = 970+10 by omega, iterT_add, trace_970]
  change iterT 10 (1911,69) = some (855,1149)
  rw [← iterFast_correct]
  decide

theorem trace_990 : iterT 990 (2,1) = some (1451,583) := by
  rw [show 990 = 980+10 by omega, iterT_add, trace_980]
  change iterT 10 (855,1149) = some (1451,583)
  rw [← iterFast_correct]
  decide

theorem trace_1000 : iterT 1000 (2,1) = some (831,1229) := by
  rw [show 1000 = 990+10 by omega, iterT_add, trace_990]
  change iterT 10 (1451,583) = some (831,1229)
  rw [← iterFast_correct]
  decide

theorem trace_1010 : iterT 1010 (2,1) = some (243,1843) := by
  rw [show 1010 = 1000+10 by omega, iterT_add, trace_1000]
  change iterT 10 (831,1229) = some (243,1843)
  rw [← iterFast_correct]
  decide

theorem trace_1020 : iterT 1020 (2,1) = some (1643,463) := by
  rw [show 1020 = 1010+10 by omega, iterT_add, trace_1010]
  change iterT 10 (243,1843) = some (1643,463)
  rw [← iterFast_correct]
  decide

theorem trace_1030 : iterT 1030 (2,1) = some (1383,751) := by
  rw [show 1030 = 1020+10 by omega, iterT_add, trace_1020]
  change iterT 10 (1643,463) = some (1383,751)
  rw [← iterFast_correct]
  decide

theorem trace_1040 : iterT 1040 (2,1) = some (1167,985) := by
  rw [show 1040 = 1030+10 by omega, iterT_add, trace_1030]
  change iterT 10 (1383,751) = some (1167,985)
  rw [← iterFast_correct]
  decide

theorem trace_1050 : iterT 1050 (2,1) = some (1419,751) := by
  rw [show 1050 = 1040+10 by omega, iterT_add, trace_1040]
  change iterT 10 (1167,985) = some (1419,751)
  rw [← iterFast_correct]
  decide

theorem trace_1060 : iterT 1060 (2,1) = some (1595,607) := by
  rw [show 1060 = 1050+10 by omega, iterT_add, trace_1050]
  change iterT 10 (1419,751) = some (1595,607)
  rw [← iterFast_correct]
  decide

theorem trace_1070 : iterT 1070 (2,1) = some (1275,951) := by
  rw [show 1070 = 1060+10 by omega, iterT_add, trace_1060]
  change iterT 10 (1595,607) = some (1275,951)
  rw [← iterFast_correct]
  decide

theorem trace_1080 : iterT 1080 (2,1) = some (335,1909) := by
  rw [show 1080 = 1070+10 by omega, iterT_add, trace_1070]
  change iterT 10 (1275,951) = some (335,1909)
  rw [← iterFast_correct]
  decide

theorem trace_1090 : iterT 1090 (2,1) = some (51,2211) := by
  rw [show 1090 = 1080+10 by omega, iterT_add, trace_1080]
  change iterT 10 (335,1909) = some (51,2211)
  rw [← iterFast_correct]
  decide

theorem trace_1100 : iterT 1100 (2,1) = some (1911,361) := by
  rw [show 1100 = 1090+10 by omega, iterT_add, trace_1090]
  change iterT 10 (51,2211) = some (1911,361)
  rw [← iterFast_correct]
  decide

theorem trace_1110 : iterT 1110 (2,1) = some (767,1533) := by
  rw [show 1110 = 1100+10 by omega, iterT_add, trace_1100]
  change iterT 10 (1911,361) = some (767,1533)
  rw [← iterFast_correct]
  decide

theorem trace_1120 : iterT 1120 (2,1) = some (563,1763) := by
  rw [show 1120 = 1110+10 by omega, iterT_add, trace_1110]
  change iterT 10 (767,1533) = some (563,1763)
  rw [← iterFast_correct]
  decide

theorem trace_1130 : iterT 1130 (2,1) = some (1567,781) := by
  rw [show 1130 = 1120+10 by omega, iterT_add, trace_1120]
  change iterT 10 (563,1763) = some (1567,781)
  rw [← iterFast_correct]
  decide

theorem trace_1140 : iterT 1140 (2,1) = some (1391,977) := by
  rw [show 1140 = 1130+10 by omega, iterT_add, trace_1130]
  change iterT 10 (1567,781) = some (1391,977)
  rw [← iterFast_correct]
  decide

theorem trace_1150 : iterT 1150 (2,1) = some (355,2035) := by
  rw [show 1150 = 1140+10 by omega, iterT_add, trace_1140]
  change iterT 10 (1391,977) = some (355,2035)
  rw [← iterFast_correct]
  decide

theorem trace_1160 : iterT 1160 (2,1) = some (1859,547) := by
  rw [show 1160 = 1150+10 by omega, iterT_add, trace_1150]
  change iterT 10 (355,2035) = some (1859,547)
  rw [← iterFast_correct]
  decide

theorem trace_1170 : iterT 1170 (2,1) = some (79,2345) := by
  rw [show 1170 = 1160+10 by omega, iterT_add, trace_1160]
  change iterT 10 (1859,547) = some (79,2345)
  rw [← iterFast_correct]
  decide

theorem trace_1180 : iterT 1180 (2,1) = some (743,1693) := by
  rw [show 1180 = 1170+10 by omega, iterT_add, trace_1170]
  change iterT 10 (79,2345) = some (743,1693)
  rw [← iterFast_correct]
  decide

theorem trace_1190 : iterT 1190 (2,1) = some (1567,889) := by
  rw [show 1190 = 1180+10 by omega, iterT_add, trace_1180]
  change iterT 10 (743,1693) = some (1567,889)
  rw [← iterFast_correct]
  decide

theorem trace_1200 : iterT 1200 (2,1) = some (1663,813) := by
  rw [show 1200 = 1190+10 by omega, iterT_add, trace_1190]
  change iterT 10 (1567,889) = some (1663,813)
  rw [← iterFast_correct]
  decide

theorem trace_1210 : iterT 1210 (2,1) = some (1095,1399) := by
  rw [show 1210 = 1200+10 by omega, iterT_add, trace_1200]
  change iterT 10 (1663,813) = some (1095,1399)
  rw [← iterFast_correct]
  decide

theorem trace_1220 : iterT 1220 (2,1) = some (2039,471) := by
  rw [show 1220 = 1210+10 by omega, iterT_add, trace_1210]
  change iterT 10 (1095,1399) = some (2039,471)
  rw [← iterFast_correct]
  decide

theorem trace_1230 : iterT 1230 (2,1) = some (311,2215) := by
  rw [show 1230 = 1220+10 by omega, iterT_add, trace_1220]
  change iterT 10 (2039,471) = some (311,2215)
  rw [← iterFast_correct]
  decide

theorem trace_1240 : iterT 1240 (2,1) = some (167,2371) := by
  rw [show 1240 = 1230+10 by omega, iterT_add, trace_1230]
  change iterT 10 (311,2215) = some (167,2371)
  rw [← iterFast_correct]
  decide

theorem trace_1250 : iterT 1250 (2,1) = some (1047,1503) := by
  rw [show 1250 = 1240+10 by omega, iterT_add, trace_1240]
  change iterT 10 (167,2371) = some (1047,1503)
  rw [← iterFast_correct]
  decide

theorem trace_1260 : iterT 1260 (2,1) = some (491,2079) := by
  rw [show 1260 = 1250+10 by omega, iterT_add, trace_1250]
  change iterT 10 (1047,1503) = some (491,2079)
  rw [← iterFast_correct]
  decide

theorem trace_1270 : iterT 1270 (2,1) = some (2007,577) := by
  rw [show 1270 = 1260+10 by omega, iterT_add, trace_1260]
  change iterT 10 (491,2079) = some (2007,577)
  rw [← iterFast_correct]
  decide

theorem trace_1280 : iterT 1280 (2,1) = some (319,2285) := by
  rw [show 1280 = 1270+10 by omega, iterT_add, trace_1270]
  change iterT 10 (2007,577) = some (319,2285)
  rw [← iterFast_correct]
  decide

theorem trace_1290 : iterT 1290 (2,1) = some (55,2561) := by
  rw [show 1290 = 1280+10 by omega, iterT_add, trace_1280]
  change iterT 10 (319,2285) = some (55,2561)
  rw [← iterFast_correct]
  decide

theorem trace_1300 : iterT 1300 (2,1) = some (2039,587) := by
  rw [show 1300 = 1290+10 by omega, iterT_add, trace_1290]
  change iterT 10 (55,2561) = some (2039,587)
  rw [← iterFast_correct]
  decide

theorem trace_1310 : iterT 1310 (2,1) = some (2495,157) := by
  rw [show 1310 = 1300+10 by omega, iterT_add, trace_1300]
  change iterT 10 (2039,587) = some (2495,157)
  rw [← iterFast_correct]
  decide

theorem trace_1320 : iterT 1320 (2,1) = some (2107,567) := by
  rw [show 1320 = 1310+10 by omega, iterT_add, trace_1310]
  change iterT 10 (2495,157) = some (2107,567)
  rw [← iterFast_correct]
  decide

theorem trace_1330 : iterT 1330 (2,1) = some (731,1967) := by
  rw [show 1330 = 1320+10 by omega, iterT_add, trace_1320]
  change iterT 10 (2107,567) = some (731,1967)
  rw [← iterFast_correct]
  decide

theorem trace_1340 : iterT 1340 (2,1) = some (2623,89) := by
  rw [show 1340 = 1330+10 by omega, iterT_add, trace_1330]
  change iterT 10 (731,1967) = some (2623,89)
  rw [← iterFast_correct]
  decide

theorem trace_1350 : iterT 1350 (2,1) = some (983,1761) := by
  rw [show 1350 = 1340+10 by omega, iterT_add, trace_1340]
  change iterT 10 (2623,89) = some (983,1761)
  rw [← iterFast_correct]
  decide

theorem trace_1360 : iterT 1360 (2,1) = some (871,1891) := by
  rw [show 1360 = 1350+10 by omega, iterT_add, trace_1350]
  change iterT 10 (983,1761) = some (871,1891)
  rw [← iterFast_correct]
  decide

theorem trace_1370 : iterT 1370 (2,1) = some (1719,1057) := by
  rw [show 1370 = 1360+10 by omega, iterT_add, trace_1360]
  change iterT 10 (871,1891) = some (1719,1057)
  rw [← iterFast_correct]
  decide

theorem trace_1380 : iterT 1380 (2,1) = some (2735,65) := by
  rw [show 1380 = 1370+10 by omega, iterT_add, trace_1370]
  change iterT 10 (1719,1057) = some (2735,65)
  rw [← iterFast_correct]
  decide

theorem trace_1390 : iterT 1390 (2,1) = some (183,2639) := by
  rw [show 1390 = 1380+10 by omega, iterT_add, trace_1380]
  change iterT 10 (2735,65) = some (183,2639)
  rw [← iterFast_correct]
  decide

theorem trace_1400 : iterT 1400 (2,1) = some (935,1899) := by
  rw [show 1400 = 1390+10 by omega, iterT_add, trace_1390]
  change iterT 10 (183,2639) = some (935,1899)
  rw [← iterFast_correct]
  decide

theorem trace_1410 : iterT 1410 (2,1) = some (2663,187) := by
  rw [show 1410 = 1400+10 by omega, iterT_add, trace_1400]
  change iterT 10 (935,1899) = some (2663,187)
  rw [← iterFast_correct]
  decide

theorem trace_1420 : iterT 1420 (2,1) = some (2055,823) := by
  rw [show 1420 = 1410+10 by omega, iterT_add, trace_1410]
  change iterT 10 (2663,187) = some (2055,823)
  rw [← iterFast_correct]
  decide

theorem trace_1430 : iterT 1430 (2,1) = some (2115,795) := by
  rw [show 1430 = 1420+10 by omega, iterT_add, trace_1420]
  change iterT 10 (2055,823) = some (2115,795)
  rw [← iterFast_correct]
  decide

theorem trace_1440 : iterT 1440 (2,1) = some (2727,203) := by
  rw [show 1440 = 1430+10 by omega, iterT_add, trace_1430]
  change iterT 10 (2115,795) = some (2727,203)
  rw [← iterFast_correct]
  decide

theorem trace_1450 : iterT 1450 (2,1) = some (775,2179) := by
  rw [show 1450 = 1440+10 by omega, iterT_add, trace_1440]
  change iterT 10 (2727,203) = some (775,2179)
  rw [← iterFast_correct]
  decide

theorem trace_1460 : iterT 1460 (2,1) = some (2743,223) := by
  rw [show 1460 = 1450+10 by omega, iterT_add, trace_1450]
  change iterT 10 (775,2179) = some (2743,223)
  rw [← iterFast_correct]
  decide

theorem trace_1470 : iterT 1470 (2,1) = some (711,2279) := by
  rw [show 1470 = 1460+10 by omega, iterT_add, trace_1460]
  change iterT 10 (2743,223) = some (711,2279)
  rw [← iterFast_correct]
  decide

theorem trace_1480 : iterT 1480 (2,1) = some (2759,253) := by
  rw [show 1480 = 1470+10 by omega, iterT_add, trace_1470]
  change iterT 10 (711,2279) = some (2759,253)
  rw [← iterFast_correct]
  decide

theorem trace_1490 : iterT 1490 (2,1) = some (519,2515) := by
  rw [show 1490 = 1480+10 by omega, iterT_add, trace_1480]
  change iterT 10 (2759,253) = some (519,2515)
  rw [← iterFast_correct]
  decide

theorem trace_1500 : iterT 1500 (2,1) = some (1079,1971) := by
  rw [show 1500 = 1490+10 by omega, iterT_add, trace_1490]
  change iterT 10 (519,2515) = some (1079,1971)
  rw [← iterFast_correct]
  decide

theorem trace_1510 : iterT 1510 (2,1) = some (1043,2035) := by
  rw [show 1510 = 1500+10 by omega, iterT_add, trace_1500]
  change iterT 10 (1079,1971) = some (1043,2035)
  rw [← iterFast_correct]
  decide

theorem trace_1520 : iterT 1520 (2,1) = some (2103,995) := by
  rw [show 1520 = 1510+10 by omega, iterT_add, trace_1510]
  change iterT 10 (1043,2035) = some (2103,995)
  rw [← iterFast_correct]
  decide

theorem trace_1530 : iterT 1530 (2,1) = some (375,2757) := by
  rw [show 1530 = 1520+10 by omega, iterT_add, trace_1520]
  change iterT 10 (2103,995) = some (375,2757)
  rw [← iterFast_correct]
  decide

theorem trace_1540 : iterT 1540 (2,1) = some (2895,257) := by
  rw [show 1540 = 1530+10 by omega, iterT_add, trace_1530]
  change iterT 10 (375,2757) = some (2895,257)
  rw [← iterFast_correct]
  decide

theorem trace_1550 : iterT 1550 (2,1) = some (1087,2089) := by
  rw [show 1550 = 1540+10 by omega, iterT_add, trace_1540]
  change iterT 10 (2895,257) = some (1087,2089)
  rw [← iterFast_correct]
  decide

theorem trace_1560 : iterT 1560 (2,1) = some (87,3105) := by
  rw [show 1560 = 1550+10 by omega, iterT_add, trace_1550]
  change iterT 10 (1087,2089) = some (87,3105)
  rw [← iterFast_correct]
  decide

theorem trace_1570 : iterT 1570 (2,1) = some (3063,139) := by
  rw [show 1570 = 1560+10 by omega, iterT_add, trace_1560]
  change iterT 10 (87,3105) = some (3063,139)
  rw [← iterFast_correct]
  decide

theorem trace_1580 : iterT 1580 (2,1) = some (267,2967) := by
  rw [show 1580 = 1570+10 by omega, iterT_add, trace_1570]
  change iterT 10 (3063,139) = some (267,2967)
  rw [← iterFast_correct]
  decide

theorem trace_1590 : iterT 1590 (2,1) = some (2831,417) := by
  rw [show 1590 = 1580+10 by omega, iterT_add, trace_1580]
  change iterT 10 (267,2967) = some (2831,417)
  rw [← iterFast_correct]
  decide

theorem trace_1600 : iterT 1600 (2,1) = some (2899,379) := by
  rw [show 1600 = 1590+10 by omega, iterT_add, trace_1590]
  change iterT 10 (2831,417) = some (2899,379)
  rw [← iterFast_correct]
  decide

theorem trace_1610 : iterT 1610 (2,1) = some (3055,241) := by
  rw [show 1610 = 1600+10 by omega, iterT_add, trace_1600]
  change iterT 10 (2899,379) = some (3055,241)
  rw [← iterFast_correct]
  decide

theorem trace_1620 : iterT 1620 (2,1) = some (2095,1225) := by
  rw [show 1620 = 1610+10 by omega, iterT_add, trace_1610]
  change iterT 10 (3055,241) = some (2095,1225)
  rw [← iterFast_correct]
  decide

theorem trace_1630 : iterT 1630 (2,1) = some (2999,335) := by
  rw [show 1630 = 1620+10 by omega, iterT_add, trace_1620]
  change iterT 10 (2095,1225) = some (2999,335)
  rw [← iterFast_correct]
  decide

theorem trace_1640 : iterT 1640 (2,1) = some (1815,1541) := by
  rw [show 1640 = 1630+10 by omega, iterT_add, trace_1630]
  change iterT 10 (2999,335) = some (1815,1541)
  rw [← iterFast_correct]
  decide

theorem trace_1650 : iterT 1650 (2,1) = some (2615,757) := by
  rw [show 1650 = 1640+10 by omega, iterT_add, trace_1640]
  change iterT 10 (1815,1541) = some (2615,757)
  rw [← iterFast_correct]
  decide

theorem trace_1660 : iterT 1660 (2,1) = some (2447,945) := by
  rw [show 1660 = 1650+10 by omega, iterT_add, trace_1650]
  change iterT 10 (2615,757) = some (2447,945)
  rw [← iterFast_correct]
  decide

theorem trace_1670 : iterT 1670 (2,1) = some (2275,1139) := by
  rw [show 1670 = 1660+10 by omega, iterT_add, trace_1660]
  change iterT 10 (2447,945) = some (2275,1139)
  rw [← iterFast_correct]
  decide

theorem trace_1680 : iterT 1680 (2,1) = some (1343,2093) := by
  rw [show 1680 = 1670+10 by omega, iterT_add, trace_1670]
  change iterT 10 (2275,1139) = some (1343,2093)
  rw [← iterFast_correct]
  decide

theorem trace_1690 : iterT 1690 (2,1) = some (1407,2045) := by
  rw [show 1690 = 1680+10 by omega, iterT_add, trace_1680]
  change iterT 10 (1343,2093) = some (1407,2045)
  rw [← iterFast_correct]
  decide

theorem trace_1700 : iterT 1700 (2,1) = some (2327,1141) := by
  rw [show 1700 = 1690+10 by omega, iterT_add, trace_1690]
  change iterT 10 (1407,2045) = some (2327,1141)
  rw [← iterFast_correct]
  decide

theorem trace_1710 : iterT 1710 (2,1) = some (695,2803) := by
  rw [show 1710 = 1700+10 by omega, iterT_add, trace_1700]
  change iterT 10 (2327,1141) = some (695,2803)
  rw [← iterFast_correct]
  decide

theorem trace_1720 : iterT 1720 (2,1) = some (2303,1213) := by
  rw [show 1720 = 1710+10 by omega, iterT_add, trace_1710]
  change iterT 10 (695,2803) = some (2303,1213)
  rw [← iterFast_correct]
  decide

theorem trace_1730 : iterT 1730 (2,1) = some (1895,1647) := by
  rw [show 1730 = 1720+10 by omega, iterT_add, trace_1720]
  change iterT 10 (2303,1213) = some (1895,1647)
  rw [← iterFast_correct]
  decide

theorem trace_1740 : iterT 1740 (2,1) = some (2271,1285) := by
  rw [show 1740 = 1730+10 by omega, iterT_add, trace_1730]
  change iterT 10 (1895,1647) = some (2271,1285)
  rw [← iterFast_correct]
  decide

theorem trace_1741 : iterT 1741 (2,1) = some (1980,1579) := by
  rw [show 1741 = 1740+1 by omega, iterT_add, trace_1740]
  change iterT 1 (2271,1285) = some (1980,1579)
  rw [← iterFast_correct]
  decide

theorem trace_1742 : iterT 1742 (2,1) = some (1983,1577) := by
  rw [show 1742 = 1741+1 by omega, iterT_add, trace_1741]
  change iterT 1 (1980,1579) = some (1983,1577)
  rw [← iterFast_correct]
  decide

theorem trace_1743 : iterT 1743 (2,1) = some (820,2743) := by
  rw [show 1743 = 1742+1 by omega, iterT_add, trace_1742]
  change iterT 1 (1983,1577) = some (820,2743)
  rw [← iterFast_correct]
  decide

theorem no_critical_0 :
    ∀ t, iterT t (2,1) ≠ some (2,critical 0) := by
  apply no_target_bracket 1 (4,0) (2,5) (2,critical 0)
  · exact trace_1
  · rw [← Tfast_correct]; decide
  · decide
  · decide
  · decide

theorem no_critical_1 :
    ∀ t, iterT t (2,1) ≠ some (2,critical 1) := by
  apply no_target_bracket 8 (0,17) (3,15) (2,critical 1)
  · exact trace_8
  · rw [← Tfast_correct]; decide
  · decide
  · decide
  · decide

theorem no_critical_2 :
    ∀ t, iterT t (2,1) ≠ some (2,critical 2) := by
  apply no_target_bracket 23 (27,15) (32,13) (2,critical 2)
  · exact trace_23
  · rw [← Tfast_correct]; decide
  · decide
  · decide
  · decide

theorem no_critical_3 :
    ∀ t, iterT t (2,1) ≠ some (2,critical 3) := by
  apply no_target_bracket 55 (8,89) (11,87) (2,critical 3)
  · exact trace_55
  · rw [← Tfast_correct]; decide
  · decide
  · decide
  · decide

theorem no_critical_4 :
    ∀ t, iterT t (2,1) ≠ some (2,critical 4) := by
  apply no_target_bracket 110 (163,43) (76,135) (2,critical 4)
  · exact trace_110
  · rw [← Tfast_correct]; decide
  · decide
  · decide
  · decide

theorem no_critical_5 :
    ∀ t, iterT t (2,1) ≠ some (2,critical 5) := by
  apply no_target_bracket 219 (272,157) (275,155) (2,critical 5)
  · exact trace_219
  · rw [← Tfast_correct]; decide
  · decide
  · decide
  · decide

theorem no_critical_6 :
    ∀ t, iterT t (2,1) ≠ some (2,critical 6) := by
  apply no_target_bracket 438 (619,255) (736,141) (2,critical 6)
  · exact trace_438
  · rw [← Tfast_correct]; decide
  · decide
  · decide
  · decide

theorem no_critical_7 :
    ∀ t, iterT t (2,1) ≠ some (2,critical 7) := by
  apply no_target_bracket 861 (152,1617) (155,1615) (2,critical 7)
  · exact trace_861
  · rw [← Tfast_correct]; decide
  · decide
  · decide
  · decide

theorem no_critical_8 :
    ∀ t, iterT t (2,1) ≠ some (2,critical 8) := by
  apply no_target_bracket 1741 (1980,1579) (1983,1577) (2,critical 8)
  · exact trace_1741
  · rw [← Tfast_correct]; decide
  · decide
  · decide
  · decide

theorem no_first_nine (i : Nat) (hi : i ≤ 8) :
    ∀ t, iterT t (2,1) ≠ some (2,critical i) := by
  have hd : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
  rcases hd with h|h|h|h|h|h|h|h|h
  all_goals subst i
  all_goals first
    | exact no_critical_0
    | exact no_critical_1
    | exact no_critical_2
    | exact no_critical_3
    | exact no_critical_4
    | exact no_critical_5
    | exact no_critical_6
    | exact no_critical_7
    | exact no_critical_8

#print axioms BB6.Agent7.no_first_nine
#print axioms BB6.Agent7.no_target_bracket
#print axioms BB6.Agent7.no_critical_0
end BB6.Agent7
