import M8TraceBridge

set_option maxRecDepth 300000
set_option maxHeartbeats 0
namespace BB6.Agent12TerminalCutoff
open BB6.Agent1M8

private theorem seg0 : runFast 10000 (some (1698114,725093)) = some (2075836,571283) := by decide +kernel
private theorem seg1 : runFast 10000 (some (2075836,571283)) = some (2973028,157610) := by decide +kernel
private theorem seg2 : runFast 10000 (some (2973028,157610)) = some (1551379,903409) := by decide +kernel
private theorem seg3 : runFast 10000 (some (1551379,903409)) = some (2512969,457818) := by decide +kernel
private theorem seg4 : runFast 10000 (some (2512969,457818)) = some (686784,1406083) := by decide +kernel
private theorem seg5 : runFast 10000 (some (686784,1406083)) = some (3322328,123263) := by decide +kernel
private theorem seg6 : runFast 10000 (some (3322328,123263)) = some (916264,1361619) := by decide +kernel
private theorem seg7 : runFast 10000 (some (916264,1361619)) = some (1031482,1338974) := by decide +kernel
private theorem seg8 : runFast 10000 (some (1031482,1338974)) = some (1996512,891555) := by decide +kernel
private theorem seg9 : runFast 10000 (some (1996512,891555)) = some (3426427,211725) := by decide +kernel
private theorem seg10 : runFast 10000 (some (3426427,211725)) = some (221526,1849234) := by decide +kernel
private theorem seg11 : runFast 10000 (some (221526,1849234)) = some (2583787,703138) := by decide +kernel
private theorem seg12 : runFast 10000 (some (2583787,703138)) = some (3129532,465462) := by decide +kernel
private theorem seg13 : runFast 10000 (some (3129532,465462)) = some (551613,1789915) := by decide +kernel
private theorem seg14 : runFast 10000 (some (551613,1789915)) = some (910957,1645252) := by decide +kernel

private theorem prefix0 : runFast 10000 (some (1698114,725093)) = some (2075836,571283) := seg0
private theorem prefix1 : runFast 20000 (some (1698114,725093)) = some (2973028,157610) := by
  calc
    runFast 20000 (some (1698114,725093)) = runFast 10000 (runFast 10000 (some (1698114,725093))) := runFast_add 10000 10000 _
    _ = _ := by rw [prefix0,seg1]
private theorem prefix2 : runFast 30000 (some (1698114,725093)) = some (1551379,903409) := by
  calc
    runFast 30000 (some (1698114,725093)) = runFast 10000 (runFast 20000 (some (1698114,725093))) := runFast_add 20000 10000 _
    _ = _ := by rw [prefix1,seg2]
private theorem prefix3 : runFast 40000 (some (1698114,725093)) = some (2512969,457818) := by
  calc
    runFast 40000 (some (1698114,725093)) = runFast 10000 (runFast 30000 (some (1698114,725093))) := runFast_add 30000 10000 _
    _ = _ := by rw [prefix2,seg3]
private theorem prefix4 : runFast 50000 (some (1698114,725093)) = some (686784,1406083) := by
  calc
    runFast 50000 (some (1698114,725093)) = runFast 10000 (runFast 40000 (some (1698114,725093))) := runFast_add 40000 10000 _
    _ = _ := by rw [prefix3,seg4]
private theorem prefix5 : runFast 60000 (some (1698114,725093)) = some (3322328,123263) := by
  calc
    runFast 60000 (some (1698114,725093)) = runFast 10000 (runFast 50000 (some (1698114,725093))) := runFast_add 50000 10000 _
    _ = _ := by rw [prefix4,seg5]
private theorem prefix6 : runFast 70000 (some (1698114,725093)) = some (916264,1361619) := by
  calc
    runFast 70000 (some (1698114,725093)) = runFast 10000 (runFast 60000 (some (1698114,725093))) := runFast_add 60000 10000 _
    _ = _ := by rw [prefix5,seg6]
private theorem prefix7 : runFast 80000 (some (1698114,725093)) = some (1031482,1338974) := by
  calc
    runFast 80000 (some (1698114,725093)) = runFast 10000 (runFast 70000 (some (1698114,725093))) := runFast_add 70000 10000 _
    _ = _ := by rw [prefix6,seg7]
private theorem prefix8 : runFast 90000 (some (1698114,725093)) = some (1996512,891555) := by
  calc
    runFast 90000 (some (1698114,725093)) = runFast 10000 (runFast 80000 (some (1698114,725093))) := runFast_add 80000 10000 _
    _ = _ := by rw [prefix7,seg8]
private theorem prefix9 : runFast 100000 (some (1698114,725093)) = some (3426427,211725) := by
  calc
    runFast 100000 (some (1698114,725093)) = runFast 10000 (runFast 90000 (some (1698114,725093))) := runFast_add 90000 10000 _
    _ = _ := by rw [prefix8,seg9]
private theorem prefix10 : runFast 110000 (some (1698114,725093)) = some (221526,1849234) := by
  calc
    runFast 110000 (some (1698114,725093)) = runFast 10000 (runFast 100000 (some (1698114,725093))) := runFast_add 100000 10000 _
    _ = _ := by rw [prefix9,seg10]
private theorem prefix11 : runFast 120000 (some (1698114,725093)) = some (2583787,703138) := by
  calc
    runFast 120000 (some (1698114,725093)) = runFast 10000 (runFast 110000 (some (1698114,725093))) := runFast_add 110000 10000 _
    _ = _ := by rw [prefix10,seg11]
private theorem prefix12 : runFast 130000 (some (1698114,725093)) = some (3129532,465462) := by
  calc
    runFast 130000 (some (1698114,725093)) = runFast 10000 (runFast 120000 (some (1698114,725093))) := runFast_add 120000 10000 _
    _ = _ := by rw [prefix11,seg12]
private theorem prefix13 : runFast 140000 (some (1698114,725093)) = some (551613,1789915) := by
  calc
    runFast 140000 (some (1698114,725093)) = runFast 10000 (runFast 130000 (some (1698114,725093))) := runFast_add 130000 10000 _
    _ = _ := by rw [prefix12,seg13]
private theorem prefix14 : runFast 150000 (some (1698114,725093)) = some (910957,1645252) := by
  calc
    runFast 150000 (some (1698114,725093)) = runFast 10000 (runFast 140000 (some (1698114,725093))) := runFast_add 140000 10000 _
    _ = _ := by rw [prefix13,seg14]

theorem part2 : runFast 150000 (some (1698114,725093)) = some (910957,1645252) := prefix14
#print axioms part2
end BB6.Agent12TerminalCutoff
