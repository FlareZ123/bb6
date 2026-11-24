import M8TraceBridge

set_option maxRecDepth 300000
set_option maxHeartbeats 0
namespace BB6.Agent12TerminalCutoff
open BB6.Agent1M8

private theorem seg0 : runFast 10000 (some (1989304,2680598)) = some (6998076,211134) := by decide +kernel
private theorem seg1 : runFast 10000 (some (6998076,211134)) = some (1469238,3010784) := by decide +kernel
private theorem seg2 : runFast 10000 (some (1469238,3010784)) = some (2875249,2342918) := by decide +kernel
private theorem seg3 : runFast 10000 (some (2875249,2342918)) = some (6318847,656134) := by decide +kernel
private theorem seg4 : runFast 10000 (some (6318847,656134)) = some (4310898,1695269) := by decide +kernel
private theorem seg5 : runFast 10000 (some (4310898,1695269)) = some (4858744,1456136) := by decide +kernel
private theorem seg6 : runFast 10000 (some (4858744,1456136)) = some (383064,3729138) := by decide +kernel
private theorem seg7 : runFast 10000 (some (383064,3729138)) = some (4214165,1848346) := by decide +kernel
private theorem seg8 : runFast 10000 (some (4214165,1848346)) = some (7454012,263556) := by decide +kernel
private theorem seg9 : runFast 10000 (some (7454012,263556)) = some (6023669,1013498) := by decide +kernel
private theorem seg10 : runFast 10000 (some (6023669,1013498)) = some (1402029,3359051) := by decide +kernel
private theorem seg11 : runFast 10000 (some (1402029,3359051)) = some (4467918,1861201) := by decide +kernel
private theorem seg12 : runFast 10000 (some (4467918,1861201)) = some (6787661,736238) := by decide +kernel
private theorem seg13 : runFast 10000 (some (6787661,736238)) = some (4873574,1727866) := by decide +kernel
private theorem seg14 : runFast 10000 (some (4873574,1727866)) = some (8025054,187249) := by decide +kernel

private theorem prefix0 : runFast 10000 (some (1989304,2680598)) = some (6998076,211134) := seg0
private theorem prefix1 : runFast 20000 (some (1989304,2680598)) = some (1469238,3010784) := by
  calc
    runFast 20000 (some (1989304,2680598)) = runFast 10000 (runFast 10000 (some (1989304,2680598))) := runFast_add 10000 10000 _
    _ = _ := by rw [prefix0,seg1]
private theorem prefix2 : runFast 30000 (some (1989304,2680598)) = some (2875249,2342918) := by
  calc
    runFast 30000 (some (1989304,2680598)) = runFast 10000 (runFast 20000 (some (1989304,2680598))) := runFast_add 20000 10000 _
    _ = _ := by rw [prefix1,seg2]
private theorem prefix3 : runFast 40000 (some (1989304,2680598)) = some (6318847,656134) := by
  calc
    runFast 40000 (some (1989304,2680598)) = runFast 10000 (runFast 30000 (some (1989304,2680598))) := runFast_add 30000 10000 _
    _ = _ := by rw [prefix2,seg3]
private theorem prefix4 : runFast 50000 (some (1989304,2680598)) = some (4310898,1695269) := by
  calc
    runFast 50000 (some (1989304,2680598)) = runFast 10000 (runFast 40000 (some (1989304,2680598))) := runFast_add 40000 10000 _
    _ = _ := by rw [prefix3,seg4]
private theorem prefix5 : runFast 60000 (some (1989304,2680598)) = some (4858744,1456136) := by
  calc
    runFast 60000 (some (1989304,2680598)) = runFast 10000 (runFast 50000 (some (1989304,2680598))) := runFast_add 50000 10000 _
    _ = _ := by rw [prefix4,seg5]
private theorem prefix6 : runFast 70000 (some (1989304,2680598)) = some (383064,3729138) := by
  calc
    runFast 70000 (some (1989304,2680598)) = runFast 10000 (runFast 60000 (some (1989304,2680598))) := runFast_add 60000 10000 _
    _ = _ := by rw [prefix5,seg6]
private theorem prefix7 : runFast 80000 (some (1989304,2680598)) = some (4214165,1848346) := by
  calc
    runFast 80000 (some (1989304,2680598)) = runFast 10000 (runFast 70000 (some (1989304,2680598))) := runFast_add 70000 10000 _
    _ = _ := by rw [prefix6,seg7]
private theorem prefix8 : runFast 90000 (some (1989304,2680598)) = some (7454012,263556) := by
  calc
    runFast 90000 (some (1989304,2680598)) = runFast 10000 (runFast 80000 (some (1989304,2680598))) := runFast_add 80000 10000 _
    _ = _ := by rw [prefix7,seg8]
private theorem prefix9 : runFast 100000 (some (1989304,2680598)) = some (6023669,1013498) := by
  calc
    runFast 100000 (some (1989304,2680598)) = runFast 10000 (runFast 90000 (some (1989304,2680598))) := runFast_add 90000 10000 _
    _ = _ := by rw [prefix8,seg9]
private theorem prefix10 : runFast 110000 (some (1989304,2680598)) = some (1402029,3359051) := by
  calc
    runFast 110000 (some (1989304,2680598)) = runFast 10000 (runFast 100000 (some (1989304,2680598))) := runFast_add 100000 10000 _
    _ = _ := by rw [prefix9,seg10]
private theorem prefix11 : runFast 120000 (some (1989304,2680598)) = some (4467918,1861201) := by
  calc
    runFast 120000 (some (1989304,2680598)) = runFast 10000 (runFast 110000 (some (1989304,2680598))) := runFast_add 110000 10000 _
    _ = _ := by rw [prefix10,seg11]
private theorem prefix12 : runFast 130000 (some (1989304,2680598)) = some (6787661,736238) := by
  calc
    runFast 130000 (some (1989304,2680598)) = runFast 10000 (runFast 120000 (some (1989304,2680598))) := runFast_add 120000 10000 _
    _ = _ := by rw [prefix11,seg12]
private theorem prefix13 : runFast 140000 (some (1989304,2680598)) = some (4873574,1727866) := by
  calc
    runFast 140000 (some (1989304,2680598)) = runFast 10000 (runFast 130000 (some (1989304,2680598))) := runFast_add 130000 10000 _
    _ = _ := by rw [prefix12,seg13]
private theorem prefix14 : runFast 150000 (some (1989304,2680598)) = some (8025054,187249) := by
  calc
    runFast 150000 (some (1989304,2680598)) = runFast 10000 (runFast 140000 (some (1989304,2680598))) := runFast_add 140000 10000 _
    _ = _ := by rw [prefix13,seg14]

theorem part6 : runFast 150000 (some (1989304,2680598)) = some (8025054,187249) := prefix14
#print axioms part6
end BB6.Agent12TerminalCutoff
