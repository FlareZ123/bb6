import Raw40LateCrossingTripleCells
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6Coverage.Agent19Raw40LateCrossing.C1REM1096
open BB6Coverage Agent42Crossing Agent19OrientedCrossing Agent50Zipper
def right0B0 : List Cell := [c337]
theorem right0B0OK : chain oriented true (edge headCell true) right0B0 (edge c337 true) := by
  apply chainB_sound
  rfl
def right0Tail0 : List Cell := right0B0
theorem right0Tail0OK : chain oriented true (edge headCell true) right0Tail0 (edge c337 true) := right0B0OK
def right0 : List Cell := right0Tail0
theorem right0OK : chain oriented true (edge headCell true) right0 (edge c337 true) := right0Tail0OK
def seg0 : Segment := ⟨right0,false,(edge c337 true)⟩
theorem pump0 : seg0.pump = true → (edge headCell true) = seg0.exit := by decide +kernel
def right1B0 : List Cell := copies [c337] 224
theorem right1B0OK : chain oriented true (edge c337 true) right1B0 (edge c337 true) := by
  have he : (edge c337 true) = (edge c337 true) := by decide +kernel
  have ho : chain oriented true (edge c337 true) [c337] (edge c337 true) := by apply chainB_sound; rfl
  simpa only [he] using (chain_copies oriented true (edge c337 true) [c337] ho 224)
def right1Tail0 : List Cell := right1B0
theorem right1Tail0OK : chain oriented true (edge c337 true) right1Tail0 (edge c337 true) := right1B0OK
def right1 : List Cell := right1Tail0
theorem right1OK : chain oriented true (edge c337 true) right1 (edge c337 true) := right1Tail0OK
def seg1 : Segment := ⟨right1,true,(edge c337 true)⟩
theorem pump1 : seg1.pump = true → (edge c337 true) = seg1.exit := by decide +kernel
def right2B0 : List Cell := copies [c337] 526
theorem right2B0OK : chain oriented true (edge c337 true) right2B0 (edge c337 true) := by
  have he : (edge c337 true) = (edge c337 true) := by decide +kernel
  have ho : chain oriented true (edge c337 true) [c337] (edge c337 true) := by apply chainB_sound; rfl
  simpa only [he] using (chain_copies oriented true (edge c337 true) [c337] ho 526)
def right2B1 : List Cell := [c338,c339,c340,c341,c342,c343]
theorem right2B1OK : chain oriented true (edge c337 true) right2B1 (edge c343 true) := by
  apply chainB_sound
  rfl
def right2B2 : List Cell := [c344,c345,c346,c347,c348,c349]
theorem right2B2OK : chain oriented true (edge c343 true) right2B2 (edge c349 true) := by
  apply chainB_sound
  rfl
def right2B3 : List Cell := [c350,c351,c352,c353,c354,c355]
theorem right2B3OK : chain oriented true (edge c349 true) right2B3 (edge c355 true) := by
  apply chainB_sound
  rfl
def right2B4 : List Cell := [c356,c357,c358,c359,c360,c361]
theorem right2B4OK : chain oriented true (edge c355 true) right2B4 (edge c361 true) := by
  apply chainB_sound
  rfl
def right2B5 : List Cell := [c362,c363,c364,c365,c366,c367]
theorem right2B5OK : chain oriented true (edge c361 true) right2B5 (edge c367 true) := by
  apply chainB_sound
  rfl
def right2B6 : List Cell := [c368,c369,c370,c371,c372,c373]
theorem right2B6OK : chain oriented true (edge c367 true) right2B6 (edge c373 true) := by
  apply chainB_sound
  rfl
def right2B7 : List Cell := [c374,c375,c376,c377,c378,c379]
theorem right2B7OK : chain oriented true (edge c373 true) right2B7 (edge c379 true) := by
  apply chainB_sound
  rfl
def right2B8 : List Cell := [c380,c381,c382,c383,c384,c385]
theorem right2B8OK : chain oriented true (edge c379 true) right2B8 (edge c385 true) := by
  apply chainB_sound
  rfl
def right2B9 : List Cell := [c386,c387,c388,c389,c390,c391]
theorem right2B9OK : chain oriented true (edge c385 true) right2B9 (edge c391 true) := by
  apply chainB_sound
  rfl
def right2B10 : List Cell := [c392,c393,c394,c395,c396,c397]
theorem right2B10OK : chain oriented true (edge c391 true) right2B10 (edge c397 true) := by
  apply chainB_sound
  rfl
def right2B11 : List Cell := [c398,c399,c400,c401,c402,c403]
theorem right2B11OK : chain oriented true (edge c397 true) right2B11 (edge c403 true) := by
  apply chainB_sound
  rfl
def right2B12 : List Cell := [c404,c405,c406,c407,c408,c409]
theorem right2B12OK : chain oriented true (edge c403 true) right2B12 (edge c409 true) := by
  apply chainB_sound
  rfl
def right2B13 : List Cell := [c410,c411,c412,c413,c414,c415]
theorem right2B13OK : chain oriented true (edge c409 true) right2B13 (edge c415 true) := by
  apply chainB_sound
  rfl
def right2B14 : List Cell := [c416,c417,c418,c419,c420,c421]
theorem right2B14OK : chain oriented true (edge c415 true) right2B14 (edge c421 true) := by
  apply chainB_sound
  rfl
def right2B15 : List Cell := [c422,c423,c424,c425,c426,c427]
theorem right2B15OK : chain oriented true (edge c421 true) right2B15 (edge c427 true) := by
  apply chainB_sound
  rfl
def right2B16 : List Cell := [c428,c429,c430,c431,c432,c433]
theorem right2B16OK : chain oriented true (edge c427 true) right2B16 (edge c433 true) := by
  apply chainB_sound
  rfl
def right2B17 : List Cell := [c434,c435,c436,c437,c438,c439]
theorem right2B17OK : chain oriented true (edge c433 true) right2B17 (edge c439 true) := by
  apply chainB_sound
  rfl
def right2B18 : List Cell := [c440,c441,c442,c443,c444,c445]
theorem right2B18OK : chain oriented true (edge c439 true) right2B18 (edge c445 true) := by
  apply chainB_sound
  rfl
def right2B19 : List Cell := [c446,c447,c448,c449,c450,c451]
theorem right2B19OK : chain oriented true (edge c445 true) right2B19 (edge c451 true) := by
  apply chainB_sound
  rfl
def right2B20 : List Cell := [c452,c453,c454,c455,c456,c457]
theorem right2B20OK : chain oriented true (edge c451 true) right2B20 (edge c457 true) := by
  apply chainB_sound
  rfl
def right2B21 : List Cell := [c458,c459,c460,c461,c462,c463]
theorem right2B21OK : chain oriented true (edge c457 true) right2B21 (edge c463 true) := by
  apply chainB_sound
  rfl
def right2B22 : List Cell := [c464,c465,c466,c467,c468,c469]
theorem right2B22OK : chain oriented true (edge c463 true) right2B22 (edge c469 true) := by
  apply chainB_sound
  rfl
def right2B23 : List Cell := [c470,c471,c472,c473,c474,c475]
theorem right2B23OK : chain oriented true (edge c469 true) right2B23 (edge c475 true) := by
  apply chainB_sound
  rfl
def right2B24 : List Cell := [c476,c477,c478,c479,c480,c481]
theorem right2B24OK : chain oriented true (edge c475 true) right2B24 (edge c481 true) := by
  apply chainB_sound
  rfl
def right2B25 : List Cell := [c482,c483,c484,c485,c486,c487]
theorem right2B25OK : chain oriented true (edge c481 true) right2B25 (edge c487 true) := by
  apply chainB_sound
  rfl
def right2B26 : List Cell := [c488,c489,c490,c491,c492,c493]
theorem right2B26OK : chain oriented true (edge c487 true) right2B26 (edge c493 true) := by
  apply chainB_sound
  rfl
def right2Tail26 : List Cell := right2B26
theorem right2Tail26OK : chain oriented true (edge c487 true) right2Tail26 (edge c493 true) := right2B26OK
def right2Tail25 : List Cell := right2B25 ++ right2Tail26
theorem right2Tail25OK : chain oriented true (edge c481 true) right2Tail25 (edge c493 true) := chain_append oriented true _ _ _ _ _ right2B25OK right2Tail26OK
def right2Tail24 : List Cell := right2B24 ++ right2Tail25
theorem right2Tail24OK : chain oriented true (edge c475 true) right2Tail24 (edge c493 true) := chain_append oriented true _ _ _ _ _ right2B24OK right2Tail25OK
def right2Tail23 : List Cell := right2B23 ++ right2Tail24
theorem right2Tail23OK : chain oriented true (edge c469 true) right2Tail23 (edge c493 true) := chain_append oriented true _ _ _ _ _ right2B23OK right2Tail24OK
def right2Tail22 : List Cell := right2B22 ++ right2Tail23
theorem right2Tail22OK : chain oriented true (edge c463 true) right2Tail22 (edge c493 true) := chain_append oriented true _ _ _ _ _ right2B22OK right2Tail23OK
def right2Tail21 : List Cell := right2B21 ++ right2Tail22
theorem right2Tail21OK : chain oriented true (edge c457 true) right2Tail21 (edge c493 true) := chain_append oriented true _ _ _ _ _ right2B21OK right2Tail22OK
def right2Tail20 : List Cell := right2B20 ++ right2Tail21
theorem right2Tail20OK : chain oriented true (edge c451 true) right2Tail20 (edge c493 true) := chain_append oriented true _ _ _ _ _ right2B20OK right2Tail21OK
def right2Tail19 : List Cell := right2B19 ++ right2Tail20
theorem right2Tail19OK : chain oriented true (edge c445 true) right2Tail19 (edge c493 true) := chain_append oriented true _ _ _ _ _ right2B19OK right2Tail20OK
def right2Tail18 : List Cell := right2B18 ++ right2Tail19
theorem right2Tail18OK : chain oriented true (edge c439 true) right2Tail18 (edge c493 true) := chain_append oriented true _ _ _ _ _ right2B18OK right2Tail19OK
def right2Tail17 : List Cell := right2B17 ++ right2Tail18
theorem right2Tail17OK : chain oriented true (edge c433 true) right2Tail17 (edge c493 true) := chain_append oriented true _ _ _ _ _ right2B17OK right2Tail18OK
def right2Tail16 : List Cell := right2B16 ++ right2Tail17
theorem right2Tail16OK : chain oriented true (edge c427 true) right2Tail16 (edge c493 true) := chain_append oriented true _ _ _ _ _ right2B16OK right2Tail17OK
def right2Tail15 : List Cell := right2B15 ++ right2Tail16
theorem right2Tail15OK : chain oriented true (edge c421 true) right2Tail15 (edge c493 true) := chain_append oriented true _ _ _ _ _ right2B15OK right2Tail16OK
def right2Tail14 : List Cell := right2B14 ++ right2Tail15
theorem right2Tail14OK : chain oriented true (edge c415 true) right2Tail14 (edge c493 true) := chain_append oriented true _ _ _ _ _ right2B14OK right2Tail15OK
def right2Tail13 : List Cell := right2B13 ++ right2Tail14
theorem right2Tail13OK : chain oriented true (edge c409 true) right2Tail13 (edge c493 true) := chain_append oriented true _ _ _ _ _ right2B13OK right2Tail14OK
def right2Tail12 : List Cell := right2B12 ++ right2Tail13
theorem right2Tail12OK : chain oriented true (edge c403 true) right2Tail12 (edge c493 true) := chain_append oriented true _ _ _ _ _ right2B12OK right2Tail13OK
def right2Tail11 : List Cell := right2B11 ++ right2Tail12
theorem right2Tail11OK : chain oriented true (edge c397 true) right2Tail11 (edge c493 true) := chain_append oriented true _ _ _ _ _ right2B11OK right2Tail12OK
def right2Tail10 : List Cell := right2B10 ++ right2Tail11
theorem right2Tail10OK : chain oriented true (edge c391 true) right2Tail10 (edge c493 true) := chain_append oriented true _ _ _ _ _ right2B10OK right2Tail11OK
def right2Tail9 : List Cell := right2B9 ++ right2Tail10
theorem right2Tail9OK : chain oriented true (edge c385 true) right2Tail9 (edge c493 true) := chain_append oriented true _ _ _ _ _ right2B9OK right2Tail10OK
def right2Tail8 : List Cell := right2B8 ++ right2Tail9
theorem right2Tail8OK : chain oriented true (edge c379 true) right2Tail8 (edge c493 true) := chain_append oriented true _ _ _ _ _ right2B8OK right2Tail9OK
def right2Tail7 : List Cell := right2B7 ++ right2Tail8
theorem right2Tail7OK : chain oriented true (edge c373 true) right2Tail7 (edge c493 true) := chain_append oriented true _ _ _ _ _ right2B7OK right2Tail8OK
def right2Tail6 : List Cell := right2B6 ++ right2Tail7
theorem right2Tail6OK : chain oriented true (edge c367 true) right2Tail6 (edge c493 true) := chain_append oriented true _ _ _ _ _ right2B6OK right2Tail7OK
def right2Tail5 : List Cell := right2B5 ++ right2Tail6
theorem right2Tail5OK : chain oriented true (edge c361 true) right2Tail5 (edge c493 true) := chain_append oriented true _ _ _ _ _ right2B5OK right2Tail6OK
def right2Tail4 : List Cell := right2B4 ++ right2Tail5
theorem right2Tail4OK : chain oriented true (edge c355 true) right2Tail4 (edge c493 true) := chain_append oriented true _ _ _ _ _ right2B4OK right2Tail5OK
def right2Tail3 : List Cell := right2B3 ++ right2Tail4
theorem right2Tail3OK : chain oriented true (edge c349 true) right2Tail3 (edge c493 true) := chain_append oriented true _ _ _ _ _ right2B3OK right2Tail4OK
def right2Tail2 : List Cell := right2B2 ++ right2Tail3
theorem right2Tail2OK : chain oriented true (edge c343 true) right2Tail2 (edge c493 true) := chain_append oriented true _ _ _ _ _ right2B2OK right2Tail3OK
def right2Tail1 : List Cell := right2B1 ++ right2Tail2
theorem right2Tail1OK : chain oriented true (edge c337 true) right2Tail1 (edge c493 true) := chain_append oriented true _ _ _ _ _ right2B1OK right2Tail2OK
def right2Tail0 : List Cell := right2B0 ++ right2Tail1
theorem right2Tail0OK : chain oriented true (edge c337 true) right2Tail0 (edge c493 true) := chain_append oriented true _ _ _ _ _ right2B0OK right2Tail1OK
def right2 : List Cell := right2Tail0
theorem right2OK : chain oriented true (edge c337 true) right2 (edge c493 true) := right2Tail0OK
def seg2 : Segment := ⟨right2,false,(edge c493 true)⟩
theorem pump2 : seg2.pump = true → (edge c337 true) = seg2.exit := by decide +kernel
def right3B0 : List Cell := [c494,c495,c496,c497,c498,c491]
theorem right3B0OK : chain oriented true (edge c493 true) right3B0 (edge c491 true) := by
  apply chainB_sound
  rfl
def right3B1 : List Cell := [c492,c493,c494,c495,c496,c497]
theorem right3B1OK : chain oriented true (edge c491 true) right3B1 (edge c497 true) := by
  apply chainB_sound
  rfl
def right3B2 : List Cell := [c498,c491,c492,c493,c494,c495]
theorem right3B2OK : chain oriented true (edge c497 true) right3B2 (edge c495 true) := by
  apply chainB_sound
  rfl
def right3B3 : List Cell := [c496,c497,c498,c491,c492,c493]
theorem right3B3OK : chain oriented true (edge c495 true) right3B3 (edge c493 true) := by
  apply chainB_sound
  rfl
def right3B4 : List Cell := [c494,c495,c496,c497,c498,c491]
theorem right3B4OK : chain oriented true (edge c493 true) right3B4 (edge c491 true) := by
  apply chainB_sound
  rfl
def right3B5 : List Cell := [c492,c493,c494,c495,c496,c497]
theorem right3B5OK : chain oriented true (edge c491 true) right3B5 (edge c497 true) := by
  apply chainB_sound
  rfl
def right3B6 : List Cell := [c498,c491,c492,c493,c494,c495]
theorem right3B6OK : chain oriented true (edge c497 true) right3B6 (edge c495 true) := by
  apply chainB_sound
  rfl
def right3B7 : List Cell := [c496,c497,c498,c491,c492,c493]
theorem right3B7OK : chain oriented true (edge c495 true) right3B7 (edge c493 true) := by
  apply chainB_sound
  rfl
def right3B8 : List Cell := [c494,c495,c496,c497,c498,c491]
theorem right3B8OK : chain oriented true (edge c493 true) right3B8 (edge c491 true) := by
  apply chainB_sound
  rfl
def right3B9 : List Cell := [c492,c493,c494,c495,c496,c497]
theorem right3B9OK : chain oriented true (edge c491 true) right3B9 (edge c497 true) := by
  apply chainB_sound
  rfl
def right3B10 : List Cell := [c498,c491,c492,c493,c494,c495]
theorem right3B10OK : chain oriented true (edge c497 true) right3B10 (edge c495 true) := by
  apply chainB_sound
  rfl
def right3B11 : List Cell := [c496,c497,c498,c491,c492,c493]
theorem right3B11OK : chain oriented true (edge c495 true) right3B11 (edge c493 true) := by
  apply chainB_sound
  rfl
def right3B12 : List Cell := [c494,c495,c496,c497,c498,c491]
theorem right3B12OK : chain oriented true (edge c493 true) right3B12 (edge c491 true) := by
  apply chainB_sound
  rfl
def right3B13 : List Cell := [c492,c493,c494,c495,c496,c497]
theorem right3B13OK : chain oriented true (edge c491 true) right3B13 (edge c497 true) := by
  apply chainB_sound
  rfl
def right3B14 : List Cell := [c498,c491,c492,c493,c494,c495]
theorem right3B14OK : chain oriented true (edge c497 true) right3B14 (edge c495 true) := by
  apply chainB_sound
  rfl
def right3B15 : List Cell := [c496,c497,c498,c491,c492,c493]
theorem right3B15OK : chain oriented true (edge c495 true) right3B15 (edge c493 true) := by
  apply chainB_sound
  rfl
def right3Tail15 : List Cell := right3B15
theorem right3Tail15OK : chain oriented true (edge c495 true) right3Tail15 (edge c493 true) := right3B15OK
def right3Tail14 : List Cell := right3B14 ++ right3Tail15
theorem right3Tail14OK : chain oriented true (edge c497 true) right3Tail14 (edge c493 true) := chain_append oriented true _ _ _ _ _ right3B14OK right3Tail15OK
def right3Tail13 : List Cell := right3B13 ++ right3Tail14
theorem right3Tail13OK : chain oriented true (edge c491 true) right3Tail13 (edge c493 true) := chain_append oriented true _ _ _ _ _ right3B13OK right3Tail14OK
def right3Tail12 : List Cell := right3B12 ++ right3Tail13
theorem right3Tail12OK : chain oriented true (edge c493 true) right3Tail12 (edge c493 true) := chain_append oriented true _ _ _ _ _ right3B12OK right3Tail13OK
def right3Tail11 : List Cell := right3B11 ++ right3Tail12
theorem right3Tail11OK : chain oriented true (edge c495 true) right3Tail11 (edge c493 true) := chain_append oriented true _ _ _ _ _ right3B11OK right3Tail12OK
def right3Tail10 : List Cell := right3B10 ++ right3Tail11
theorem right3Tail10OK : chain oriented true (edge c497 true) right3Tail10 (edge c493 true) := chain_append oriented true _ _ _ _ _ right3B10OK right3Tail11OK
def right3Tail9 : List Cell := right3B9 ++ right3Tail10
theorem right3Tail9OK : chain oriented true (edge c491 true) right3Tail9 (edge c493 true) := chain_append oriented true _ _ _ _ _ right3B9OK right3Tail10OK
def right3Tail8 : List Cell := right3B8 ++ right3Tail9
theorem right3Tail8OK : chain oriented true (edge c493 true) right3Tail8 (edge c493 true) := chain_append oriented true _ _ _ _ _ right3B8OK right3Tail9OK
def right3Tail7 : List Cell := right3B7 ++ right3Tail8
theorem right3Tail7OK : chain oriented true (edge c495 true) right3Tail7 (edge c493 true) := chain_append oriented true _ _ _ _ _ right3B7OK right3Tail8OK
def right3Tail6 : List Cell := right3B6 ++ right3Tail7
theorem right3Tail6OK : chain oriented true (edge c497 true) right3Tail6 (edge c493 true) := chain_append oriented true _ _ _ _ _ right3B6OK right3Tail7OK
def right3Tail5 : List Cell := right3B5 ++ right3Tail6
theorem right3Tail5OK : chain oriented true (edge c491 true) right3Tail5 (edge c493 true) := chain_append oriented true _ _ _ _ _ right3B5OK right3Tail6OK
def right3Tail4 : List Cell := right3B4 ++ right3Tail5
theorem right3Tail4OK : chain oriented true (edge c493 true) right3Tail4 (edge c493 true) := chain_append oriented true _ _ _ _ _ right3B4OK right3Tail5OK
def right3Tail3 : List Cell := right3B3 ++ right3Tail4
theorem right3Tail3OK : chain oriented true (edge c495 true) right3Tail3 (edge c493 true) := chain_append oriented true _ _ _ _ _ right3B3OK right3Tail4OK
def right3Tail2 : List Cell := right3B2 ++ right3Tail3
theorem right3Tail2OK : chain oriented true (edge c497 true) right3Tail2 (edge c493 true) := chain_append oriented true _ _ _ _ _ right3B2OK right3Tail3OK
def right3Tail1 : List Cell := right3B1 ++ right3Tail2
theorem right3Tail1OK : chain oriented true (edge c491 true) right3Tail1 (edge c493 true) := chain_append oriented true _ _ _ _ _ right3B1OK right3Tail2OK
def right3Tail0 : List Cell := right3B0 ++ right3Tail1
theorem right3Tail0OK : chain oriented true (edge c493 true) right3Tail0 (edge c493 true) := chain_append oriented true _ _ _ _ _ right3B0OK right3Tail1OK
def right3 : List Cell := right3Tail0
theorem right3OK : chain oriented true (edge c493 true) right3 (edge c493 true) := right3Tail0OK
def seg3 : Segment := ⟨right3,true,(edge c493 true)⟩
theorem pump3 : seg3.pump = true → (edge c493 true) = seg3.exit := by decide +kernel

end BB6Coverage.Agent19Raw40LateCrossing.C1REM1096
