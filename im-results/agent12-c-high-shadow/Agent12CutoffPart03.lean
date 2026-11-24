import M8TraceBridge

set_option maxRecDepth 300000
set_option maxHeartbeats 0
namespace BB6.Agent12TerminalCutoff
open BB6.Agent1M8

private theorem seg0 : runFast 10000 (some (910957,1645252)) = some (4045506,113264) := by decide +kernel
private theorem seg1 : runFast 10000 (some (4045506,113264)) = some (798003,1771858) := by decide +kernel
private theorem seg2 : runFast 10000 (some (798003,1771858)) = some (4120284,145242) := by decide +kernel
private theorem seg3 : runFast 10000 (some (4120284,145242)) = some (3667000,407100) := by decide +kernel
private theorem seg4 : runFast 10000 (some (3667000,407100)) = some (3642607,454205) := by decide +kernel
private theorem seg5 : runFast 10000 (some (3642607,454205)) = some (3457033,581594) := by decide +kernel
private theorem seg6 : runFast 10000 (some (3457033,581594)) = some (4304636,192899) := by decide +kernel
private theorem seg7 : runFast 10000 (some (4304636,192899)) = some (2492325,1134428) := by decide +kernel
private theorem seg8 : runFast 10000 (some (2492325,1134428)) = some (4214767,307889) := by decide +kernel
private theorem seg9 : runFast 10000 (some (4214767,307889)) = some (4628911,135949) := by decide +kernel
private theorem seg10 : runFast 10000 (some (4628911,135949)) = some (800259,2085458) := by decide +kernel
private theorem seg11 : runFast 10000 (some (800259,2085458)) = some (708364,2166284) := by decide +kernel
private theorem seg12 : runFast 10000 (some (708364,2166284)) = some (1926106,1592254) := by decide +kernel
private theorem seg13 : runFast 10000 (some (1926106,1592254)) = some (1504994,1837846) := by decide +kernel
private theorem seg14 : runFast 10000 (some (1504994,1837846)) = some (3290029,980087) := by decide +kernel

private theorem prefix0 : runFast 10000 (some (910957,1645252)) = some (4045506,113264) := seg0
private theorem prefix1 : runFast 20000 (some (910957,1645252)) = some (798003,1771858) := by
  calc
    runFast 20000 (some (910957,1645252)) = runFast 10000 (runFast 10000 (some (910957,1645252))) := runFast_add 10000 10000 _
    _ = _ := by rw [prefix0,seg1]
private theorem prefix2 : runFast 30000 (some (910957,1645252)) = some (4120284,145242) := by
  calc
    runFast 30000 (some (910957,1645252)) = runFast 10000 (runFast 20000 (some (910957,1645252))) := runFast_add 20000 10000 _
    _ = _ := by rw [prefix1,seg2]
private theorem prefix3 : runFast 40000 (some (910957,1645252)) = some (3667000,407100) := by
  calc
    runFast 40000 (some (910957,1645252)) = runFast 10000 (runFast 30000 (some (910957,1645252))) := runFast_add 30000 10000 _
    _ = _ := by rw [prefix2,seg3]
private theorem prefix4 : runFast 50000 (some (910957,1645252)) = some (3642607,454205) := by
  calc
    runFast 50000 (some (910957,1645252)) = runFast 10000 (runFast 40000 (some (910957,1645252))) := runFast_add 40000 10000 _
    _ = _ := by rw [prefix3,seg4]
private theorem prefix5 : runFast 60000 (some (910957,1645252)) = some (3457033,581594) := by
  calc
    runFast 60000 (some (910957,1645252)) = runFast 10000 (runFast 50000 (some (910957,1645252))) := runFast_add 50000 10000 _
    _ = _ := by rw [prefix4,seg5]
private theorem prefix6 : runFast 70000 (some (910957,1645252)) = some (4304636,192899) := by
  calc
    runFast 70000 (some (910957,1645252)) = runFast 10000 (runFast 60000 (some (910957,1645252))) := runFast_add 60000 10000 _
    _ = _ := by rw [prefix5,seg6]
private theorem prefix7 : runFast 80000 (some (910957,1645252)) = some (2492325,1134428) := by
  calc
    runFast 80000 (some (910957,1645252)) = runFast 10000 (runFast 70000 (some (910957,1645252))) := runFast_add 70000 10000 _
    _ = _ := by rw [prefix6,seg7]
private theorem prefix8 : runFast 90000 (some (910957,1645252)) = some (4214767,307889) := by
  calc
    runFast 90000 (some (910957,1645252)) = runFast 10000 (runFast 80000 (some (910957,1645252))) := runFast_add 80000 10000 _
    _ = _ := by rw [prefix7,seg8]
private theorem prefix9 : runFast 100000 (some (910957,1645252)) = some (4628911,135949) := by
  calc
    runFast 100000 (some (910957,1645252)) = runFast 10000 (runFast 90000 (some (910957,1645252))) := runFast_add 90000 10000 _
    _ = _ := by rw [prefix8,seg9]
private theorem prefix10 : runFast 110000 (some (910957,1645252)) = some (800259,2085458) := by
  calc
    runFast 110000 (some (910957,1645252)) = runFast 10000 (runFast 100000 (some (910957,1645252))) := runFast_add 100000 10000 _
    _ = _ := by rw [prefix9,seg10]
private theorem prefix11 : runFast 120000 (some (910957,1645252)) = some (708364,2166284) := by
  calc
    runFast 120000 (some (910957,1645252)) = runFast 10000 (runFast 110000 (some (910957,1645252))) := runFast_add 110000 10000 _
    _ = _ := by rw [prefix10,seg11]
private theorem prefix12 : runFast 130000 (some (910957,1645252)) = some (1926106,1592254) := by
  calc
    runFast 130000 (some (910957,1645252)) = runFast 10000 (runFast 120000 (some (910957,1645252))) := runFast_add 120000 10000 _
    _ = _ := by rw [prefix11,seg12]
private theorem prefix13 : runFast 140000 (some (910957,1645252)) = some (1504994,1837846) := by
  calc
    runFast 140000 (some (910957,1645252)) = runFast 10000 (runFast 130000 (some (910957,1645252))) := runFast_add 130000 10000 _
    _ = _ := by rw [prefix12,seg13]
private theorem prefix14 : runFast 150000 (some (910957,1645252)) = some (3290029,980087) := by
  calc
    runFast 150000 (some (910957,1645252)) = runFast 10000 (runFast 140000 (some (910957,1645252))) := runFast_add 140000 10000 _
    _ = _ := by rw [prefix13,seg14]

theorem part3 : runFast 150000 (some (910957,1645252)) = some (3290029,980087) := prefix14
#print axioms part3
end BB6.Agent12TerminalCutoff
