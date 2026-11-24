import M8TraceBridge

set_option maxRecDepth 300000
set_option maxHeartbeats 0
namespace BB6.Agent12TerminalCutoff
open BB6.Agent1M8

private theorem seg0 : runFast 10000 (some (5173120,564704)) = some (2375129,1998758) := by decide +kernel
private theorem seg1 : runFast 10000 (some (2375129,1998758)) = some (2342636,2049703) := by decide +kernel
private theorem seg2 : runFast 10000 (some (2342636,2049703)) = some (3820950,1345057) := by decide +kernel
private theorem seg3 : runFast 10000 (some (3820950,1345057)) = some (5894906,343157) := by decide +kernel
private theorem seg4 : runFast 10000 (some (5894906,343157)) = some (6051392,299944) := by decide +kernel
private theorem seg5 : runFast 10000 (some (6051392,299944)) = some (370268,3175671) := by decide +kernel
private theorem seg6 : runFast 10000 (some (370268,3175671)) = some (3268929,1761246) := by decide +kernel
private theorem seg7 : runFast 10000 (some (3268929,1761246)) = some (3718481,1571158) := by decide +kernel
private theorem seg8 : runFast 10000 (some (3718481,1571158)) = some (4464380,1233219) := by decide +kernel
private theorem seg9 : runFast 10000 (some (4464380,1233219)) = some (4156236,1422243) := by decide +kernel
private theorem seg10 : runFast 10000 (some (4156236,1422243)) = some (6216034,427512) := by decide +kernel
private theorem seg11 : runFast 10000 (some (6216034,427512)) = some (5666801,737094) := by decide +kernel
private theorem seg12 : runFast 10000 (some (5666801,737094)) = some (906954,3152061) := by decide +kernel
private theorem seg13 : runFast 10000 (some (906954,3152061)) = some (5684985,798119) := by decide +kernel
private theorem seg14 : runFast 10000 (some (5684985,798119)) = some (1989304,2680598) := by decide +kernel

private theorem prefix0 : runFast 10000 (some (5173120,564704)) = some (2375129,1998758) := seg0
private theorem prefix1 : runFast 20000 (some (5173120,564704)) = some (2342636,2049703) := by
  calc
    runFast 20000 (some (5173120,564704)) = runFast 10000 (runFast 10000 (some (5173120,564704))) := runFast_add 10000 10000 _
    _ = _ := by rw [prefix0,seg1]
private theorem prefix2 : runFast 30000 (some (5173120,564704)) = some (3820950,1345057) := by
  calc
    runFast 30000 (some (5173120,564704)) = runFast 10000 (runFast 20000 (some (5173120,564704))) := runFast_add 20000 10000 _
    _ = _ := by rw [prefix1,seg2]
private theorem prefix3 : runFast 40000 (some (5173120,564704)) = some (5894906,343157) := by
  calc
    runFast 40000 (some (5173120,564704)) = runFast 10000 (runFast 30000 (some (5173120,564704))) := runFast_add 30000 10000 _
    _ = _ := by rw [prefix2,seg3]
private theorem prefix4 : runFast 50000 (some (5173120,564704)) = some (6051392,299944) := by
  calc
    runFast 50000 (some (5173120,564704)) = runFast 10000 (runFast 40000 (some (5173120,564704))) := runFast_add 40000 10000 _
    _ = _ := by rw [prefix3,seg4]
private theorem prefix5 : runFast 60000 (some (5173120,564704)) = some (370268,3175671) := by
  calc
    runFast 60000 (some (5173120,564704)) = runFast 10000 (runFast 50000 (some (5173120,564704))) := runFast_add 50000 10000 _
    _ = _ := by rw [prefix4,seg5]
private theorem prefix6 : runFast 70000 (some (5173120,564704)) = some (3268929,1761246) := by
  calc
    runFast 70000 (some (5173120,564704)) = runFast 10000 (runFast 60000 (some (5173120,564704))) := runFast_add 60000 10000 _
    _ = _ := by rw [prefix5,seg6]
private theorem prefix7 : runFast 80000 (some (5173120,564704)) = some (3718481,1571158) := by
  calc
    runFast 80000 (some (5173120,564704)) = runFast 10000 (runFast 70000 (some (5173120,564704))) := runFast_add 70000 10000 _
    _ = _ := by rw [prefix6,seg7]
private theorem prefix8 : runFast 90000 (some (5173120,564704)) = some (4464380,1233219) := by
  calc
    runFast 90000 (some (5173120,564704)) = runFast 10000 (runFast 80000 (some (5173120,564704))) := runFast_add 80000 10000 _
    _ = _ := by rw [prefix7,seg8]
private theorem prefix9 : runFast 100000 (some (5173120,564704)) = some (4156236,1422243) := by
  calc
    runFast 100000 (some (5173120,564704)) = runFast 10000 (runFast 90000 (some (5173120,564704))) := runFast_add 90000 10000 _
    _ = _ := by rw [prefix8,seg9]
private theorem prefix10 : runFast 110000 (some (5173120,564704)) = some (6216034,427512) := by
  calc
    runFast 110000 (some (5173120,564704)) = runFast 10000 (runFast 100000 (some (5173120,564704))) := runFast_add 100000 10000 _
    _ = _ := by rw [prefix9,seg10]
private theorem prefix11 : runFast 120000 (some (5173120,564704)) = some (5666801,737094) := by
  calc
    runFast 120000 (some (5173120,564704)) = runFast 10000 (runFast 110000 (some (5173120,564704))) := runFast_add 110000 10000 _
    _ = _ := by rw [prefix10,seg11]
private theorem prefix12 : runFast 130000 (some (5173120,564704)) = some (906954,3152061) := by
  calc
    runFast 130000 (some (5173120,564704)) = runFast 10000 (runFast 120000 (some (5173120,564704))) := runFast_add 120000 10000 _
    _ = _ := by rw [prefix11,seg12]
private theorem prefix13 : runFast 140000 (some (5173120,564704)) = some (5684985,798119) := by
  calc
    runFast 140000 (some (5173120,564704)) = runFast 10000 (runFast 130000 (some (5173120,564704))) := runFast_add 130000 10000 _
    _ = _ := by rw [prefix12,seg13]
private theorem prefix14 : runFast 150000 (some (5173120,564704)) = some (1989304,2680598) := by
  calc
    runFast 150000 (some (5173120,564704)) = runFast 10000 (runFast 140000 (some (5173120,564704))) := runFast_add 140000 10000 _
    _ = _ := by rw [prefix13,seg14]

theorem part5 : runFast 150000 (some (5173120,564704)) = some (1989304,2680598) := prefix14
#print axioms part5
end BB6.Agent12TerminalCutoff
