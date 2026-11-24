import M8TraceBridge

set_option maxRecDepth 300000
set_option maxHeartbeats 0
namespace BB6.Agent12TerminalCutoff
open BB6.Agent1M8

private theorem seg0 : runFast 10000 (some (4519072,3517676)) = some (3502350,4061082) := by decide +kernel
private theorem seg1 : runFast 10000 (some (3502350,4061082)) = some (1558400,5068512) := by decide +kernel
private theorem seg2 : runFast 10000 (some (1558400,5068512)) = some (7937528,1914218) := by decide +kernel
private theorem seg3 : runFast 10000 (some (7937528,1914218)) = some (2398195,4719078) := by decide +kernel
private theorem seg4 : runFast 10000 (some (2398195,4719078)) = some (2093931,4906105) := by decide +kernel
private theorem seg5 : runFast 10000 (some (2093931,4906105)) = some (8849029,1563508) := by decide +kernel
private theorem seg6 : runFast 10000 (some (8849029,1563508)) = some (1804162,5121261) := by decide +kernel
private theorem seg7 : runFast 10000 (some (1804162,5121261)) = some (4984813,3565676) := by decide +kernel
private theorem seg8 : runFast 10000 (some (4984813,3565676)) = some (4476565,3854620) := by decide +kernel
private theorem seg9 : runFast 10000 (some (4476565,3854620)) = some (2845234,4705410) := by decide +kernel
private theorem seg10 : runFast 10000 (some (2845234,4705410)) = some (1978895,5173602) := by decide +kernel
private theorem seg11 : runFast 10000 (some (1978895,5173602)) = some (10814863,790246) := by decide +kernel
private theorem seg12 : runFast 10000 (some (10814863,790246)) = some (10306990,1079274) := by decide +kernel
private theorem seg13 : runFast 10000 (some (10306990,1079274)) = some (6430239,3052168) := by decide +kernel
private theorem seg14 : runFast 10000 (some (6430239,3052168)) = some (8140864,2231926) := by decide +kernel

private theorem prefix0 : runFast 10000 (some (4519072,3517676)) = some (3502350,4061082) := seg0
private theorem prefix1 : runFast 20000 (some (4519072,3517676)) = some (1558400,5068512) := by
  calc
    runFast 20000 (some (4519072,3517676)) = runFast 10000 (runFast 10000 (some (4519072,3517676))) := runFast_add 10000 10000 _
    _ = _ := by rw [prefix0,seg1]
private theorem prefix2 : runFast 30000 (some (4519072,3517676)) = some (7937528,1914218) := by
  calc
    runFast 30000 (some (4519072,3517676)) = runFast 10000 (runFast 20000 (some (4519072,3517676))) := runFast_add 20000 10000 _
    _ = _ := by rw [prefix1,seg2]
private theorem prefix3 : runFast 40000 (some (4519072,3517676)) = some (2398195,4719078) := by
  calc
    runFast 40000 (some (4519072,3517676)) = runFast 10000 (runFast 30000 (some (4519072,3517676))) := runFast_add 30000 10000 _
    _ = _ := by rw [prefix2,seg3]
private theorem prefix4 : runFast 50000 (some (4519072,3517676)) = some (2093931,4906105) := by
  calc
    runFast 50000 (some (4519072,3517676)) = runFast 10000 (runFast 40000 (some (4519072,3517676))) := runFast_add 40000 10000 _
    _ = _ := by rw [prefix3,seg4]
private theorem prefix5 : runFast 60000 (some (4519072,3517676)) = some (8849029,1563508) := by
  calc
    runFast 60000 (some (4519072,3517676)) = runFast 10000 (runFast 50000 (some (4519072,3517676))) := runFast_add 50000 10000 _
    _ = _ := by rw [prefix4,seg5]
private theorem prefix6 : runFast 70000 (some (4519072,3517676)) = some (1804162,5121261) := by
  calc
    runFast 70000 (some (4519072,3517676)) = runFast 10000 (runFast 60000 (some (4519072,3517676))) := runFast_add 60000 10000 _
    _ = _ := by rw [prefix5,seg6]
private theorem prefix7 : runFast 80000 (some (4519072,3517676)) = some (4984813,3565676) := by
  calc
    runFast 80000 (some (4519072,3517676)) = runFast 10000 (runFast 70000 (some (4519072,3517676))) := runFast_add 70000 10000 _
    _ = _ := by rw [prefix6,seg7]
private theorem prefix8 : runFast 90000 (some (4519072,3517676)) = some (4476565,3854620) := by
  calc
    runFast 90000 (some (4519072,3517676)) = runFast 10000 (runFast 80000 (some (4519072,3517676))) := runFast_add 80000 10000 _
    _ = _ := by rw [prefix7,seg8]
private theorem prefix9 : runFast 100000 (some (4519072,3517676)) = some (2845234,4705410) := by
  calc
    runFast 100000 (some (4519072,3517676)) = runFast 10000 (runFast 90000 (some (4519072,3517676))) := runFast_add 90000 10000 _
    _ = _ := by rw [prefix8,seg9]
private theorem prefix10 : runFast 110000 (some (4519072,3517676)) = some (1978895,5173602) := by
  calc
    runFast 110000 (some (4519072,3517676)) = runFast 10000 (runFast 100000 (some (4519072,3517676))) := runFast_add 100000 10000 _
    _ = _ := by rw [prefix9,seg10]
private theorem prefix11 : runFast 120000 (some (4519072,3517676)) = some (10814863,790246) := by
  calc
    runFast 120000 (some (4519072,3517676)) = runFast 10000 (runFast 110000 (some (4519072,3517676))) := runFast_add 110000 10000 _
    _ = _ := by rw [prefix10,seg11]
private theorem prefix12 : runFast 130000 (some (4519072,3517676)) = some (10306990,1079274) := by
  calc
    runFast 130000 (some (4519072,3517676)) = runFast 10000 (runFast 120000 (some (4519072,3517676))) := runFast_add 120000 10000 _
    _ = _ := by rw [prefix11,seg12]
private theorem prefix13 : runFast 140000 (some (4519072,3517676)) = some (6430239,3052168) := by
  calc
    runFast 140000 (some (4519072,3517676)) = runFast 10000 (runFast 130000 (some (4519072,3517676))) := runFast_add 130000 10000 _
    _ = _ := by rw [prefix12,seg13]
private theorem prefix14 : runFast 150000 (some (4519072,3517676)) = some (8140864,2231926) := by
  calc
    runFast 150000 (some (4519072,3517676)) = runFast 10000 (runFast 140000 (some (4519072,3517676))) := runFast_add 140000 10000 _
    _ = _ := by rw [prefix13,seg14]

theorem part10 : runFast 150000 (some (4519072,3517676)) = some (8140864,2231926) := prefix14
#print axioms part10
end BB6.Agent12TerminalCutoff
