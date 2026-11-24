import M8TraceBridge

set_option maxRecDepth 300000
set_option maxHeartbeats 0
namespace BB6.Agent12TerminalCutoff
open BB6.Agent1M8

private theorem seg0 : runFast 10000 (some (1614262,242598)) = some (676989,746290) := by decide +kernel
private theorem seg1 : runFast 10000 (some (676989,746290)) = some (1620424,309682) := by decide +kernel
private theorem seg2 : runFast 10000 (some (1620424,309682)) = some (2231384,38998) := by decide +kernel
private theorem seg3 : runFast 10000 (some (2231384,38998)) = some (1803752,288351) := by decide +kernel
private theorem seg4 : runFast 10000 (some (1803752,288351)) = some (1080099,685137) := by decide +kernel
private theorem seg5 : runFast 10000 (some (1080099,685137)) = some (2108075,206104) := by decide +kernel
private theorem seg6 : runFast 10000 (some (2108075,206104)) = some (1399340,595143) := by decide +kernel
private theorem seg7 : runFast 10000 (some (1399340,595143)) = some (1336235,661490) := by decide +kernel
private theorem seg8 : runFast 10000 (some (1336235,661490)) = some (477231,1126433) := by decide +kernel
private theorem seg9 : runFast 10000 (some (477231,1126433)) = some (1463153,668262) := by decide +kernel
private theorem seg10 : runFast 10000 (some (1463153,668262)) = some (1801255,533857) := by decide +kernel
private theorem seg11 : runFast 10000 (some (1801255,533857)) = some (1929647,504358) := by decide +kernel
private theorem seg12 : runFast 10000 (some (1929647,504358)) = some (1619447,694302) := by decide +kernel
private theorem seg13 : runFast 10000 (some (1619447,694302)) = some (499476,1289406) := by decide +kernel
private theorem seg14 : runFast 10000 (some (499476,1289406)) = some (1698114,725093) := by decide +kernel

private theorem prefix0 : runFast 10000 (some (1614262,242598)) = some (676989,746290) := seg0
private theorem prefix1 : runFast 20000 (some (1614262,242598)) = some (1620424,309682) := by
  calc
    runFast 20000 (some (1614262,242598)) = runFast 10000 (runFast 10000 (some (1614262,242598))) := runFast_add 10000 10000 _
    _ = _ := by rw [prefix0,seg1]
private theorem prefix2 : runFast 30000 (some (1614262,242598)) = some (2231384,38998) := by
  calc
    runFast 30000 (some (1614262,242598)) = runFast 10000 (runFast 20000 (some (1614262,242598))) := runFast_add 20000 10000 _
    _ = _ := by rw [prefix1,seg2]
private theorem prefix3 : runFast 40000 (some (1614262,242598)) = some (1803752,288351) := by
  calc
    runFast 40000 (some (1614262,242598)) = runFast 10000 (runFast 30000 (some (1614262,242598))) := runFast_add 30000 10000 _
    _ = _ := by rw [prefix2,seg3]
private theorem prefix4 : runFast 50000 (some (1614262,242598)) = some (1080099,685137) := by
  calc
    runFast 50000 (some (1614262,242598)) = runFast 10000 (runFast 40000 (some (1614262,242598))) := runFast_add 40000 10000 _
    _ = _ := by rw [prefix3,seg4]
private theorem prefix5 : runFast 60000 (some (1614262,242598)) = some (2108075,206104) := by
  calc
    runFast 60000 (some (1614262,242598)) = runFast 10000 (runFast 50000 (some (1614262,242598))) := runFast_add 50000 10000 _
    _ = _ := by rw [prefix4,seg5]
private theorem prefix6 : runFast 70000 (some (1614262,242598)) = some (1399340,595143) := by
  calc
    runFast 70000 (some (1614262,242598)) = runFast 10000 (runFast 60000 (some (1614262,242598))) := runFast_add 60000 10000 _
    _ = _ := by rw [prefix5,seg6]
private theorem prefix7 : runFast 80000 (some (1614262,242598)) = some (1336235,661490) := by
  calc
    runFast 80000 (some (1614262,242598)) = runFast 10000 (runFast 70000 (some (1614262,242598))) := runFast_add 70000 10000 _
    _ = _ := by rw [prefix6,seg7]
private theorem prefix8 : runFast 90000 (some (1614262,242598)) = some (477231,1126433) := by
  calc
    runFast 90000 (some (1614262,242598)) = runFast 10000 (runFast 80000 (some (1614262,242598))) := runFast_add 80000 10000 _
    _ = _ := by rw [prefix7,seg8]
private theorem prefix9 : runFast 100000 (some (1614262,242598)) = some (1463153,668262) := by
  calc
    runFast 100000 (some (1614262,242598)) = runFast 10000 (runFast 90000 (some (1614262,242598))) := runFast_add 90000 10000 _
    _ = _ := by rw [prefix8,seg9]
private theorem prefix10 : runFast 110000 (some (1614262,242598)) = some (1801255,533857) := by
  calc
    runFast 110000 (some (1614262,242598)) = runFast 10000 (runFast 100000 (some (1614262,242598))) := runFast_add 100000 10000 _
    _ = _ := by rw [prefix9,seg10]
private theorem prefix11 : runFast 120000 (some (1614262,242598)) = some (1929647,504358) := by
  calc
    runFast 120000 (some (1614262,242598)) = runFast 10000 (runFast 110000 (some (1614262,242598))) := runFast_add 110000 10000 _
    _ = _ := by rw [prefix10,seg11]
private theorem prefix12 : runFast 130000 (some (1614262,242598)) = some (1619447,694302) := by
  calc
    runFast 130000 (some (1614262,242598)) = runFast 10000 (runFast 120000 (some (1614262,242598))) := runFast_add 120000 10000 _
    _ = _ := by rw [prefix11,seg12]
private theorem prefix13 : runFast 140000 (some (1614262,242598)) = some (499476,1289406) := by
  calc
    runFast 140000 (some (1614262,242598)) = runFast 10000 (runFast 130000 (some (1614262,242598))) := runFast_add 130000 10000 _
    _ = _ := by rw [prefix12,seg13]
private theorem prefix14 : runFast 150000 (some (1614262,242598)) = some (1698114,725093) := by
  calc
    runFast 150000 (some (1614262,242598)) = runFast 10000 (runFast 140000 (some (1614262,242598))) := runFast_add 140000 10000 _
    _ = _ := by rw [prefix13,seg14]

theorem part1 : runFast 150000 (some (1614262,242598)) = some (1698114,725093) := prefix14
#print axioms part1
end BB6.Agent12TerminalCutoff
