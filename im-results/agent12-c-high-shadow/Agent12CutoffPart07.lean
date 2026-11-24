import M8TraceBridge

set_option maxRecDepth 300000
set_option maxHeartbeats 0
namespace BB6.Agent12TerminalCutoff
open BB6.Agent1M8

private theorem seg0 : runFast 10000 (some (8025054,187249)) = some (2448192,3011019) := by decide +kernel
private theorem seg1 : runFast 10000 (some (2448192,3011019)) = some (151248,4194611) := by decide +kernel
private theorem seg2 : runFast 10000 (some (151248,4194611)) = some (86143,4262336) := by decide +kernel
private theorem seg3 : runFast 10000 (some (86143,4262336)) = some (3406205,2637290) := by decide +kernel
private theorem seg4 : runFast 10000 (some (3406205,2637290)) = some (1764568,3493164) := by decide +kernel
private theorem seg5 : runFast 10000 (some (1764568,3493164)) = some (2101901,3359670) := by decide +kernel
private theorem seg6 : runFast 10000 (some (2101901,3359670)) = some (273203,4309493) := by decide +kernel
private theorem seg7 : runFast 10000 (some (273203,4309493)) = some (8723202,119714) := by decide +kernel
private theorem seg8 : runFast 10000 (some (8723202,119714)) = some (7400772,816268) := by decide +kernel
private theorem seg9 : runFast 10000 (some (7400772,816268)) = some (8899188,102006) := by decide +kernel
private theorem seg10 : runFast 10000 (some (8899188,102006)) = some (4907210,2132497) := by decide +kernel
private theorem seg11 : runFast 10000 (some (4907210,2132497)) = some (7547038,847658) := by decide +kernel
private theorem seg12 : runFast 10000 (some (7547038,847658)) = some (4961225,2175614) := by decide +kernel
private theorem seg13 : runFast 10000 (some (4961225,2175614)) = some (627231,4377830) := by decide +kernel
private theorem seg14 : runFast 10000 (some (627231,4377830)) = some (7099237,1176830) := by decide +kernel

private theorem prefix0 : runFast 10000 (some (8025054,187249)) = some (2448192,3011019) := seg0
private theorem prefix1 : runFast 20000 (some (8025054,187249)) = some (151248,4194611) := by
  calc
    runFast 20000 (some (8025054,187249)) = runFast 10000 (runFast 10000 (some (8025054,187249))) := runFast_add 10000 10000 _
    _ = _ := by rw [prefix0,seg1]
private theorem prefix2 : runFast 30000 (some (8025054,187249)) = some (86143,4262336) := by
  calc
    runFast 30000 (some (8025054,187249)) = runFast 10000 (runFast 20000 (some (8025054,187249))) := runFast_add 20000 10000 _
    _ = _ := by rw [prefix1,seg2]
private theorem prefix3 : runFast 40000 (some (8025054,187249)) = some (3406205,2637290) := by
  calc
    runFast 40000 (some (8025054,187249)) = runFast 10000 (runFast 30000 (some (8025054,187249))) := runFast_add 30000 10000 _
    _ = _ := by rw [prefix2,seg3]
private theorem prefix4 : runFast 50000 (some (8025054,187249)) = some (1764568,3493164) := by
  calc
    runFast 50000 (some (8025054,187249)) = runFast 10000 (runFast 40000 (some (8025054,187249))) := runFast_add 40000 10000 _
    _ = _ := by rw [prefix3,seg4]
private theorem prefix5 : runFast 60000 (some (8025054,187249)) = some (2101901,3359670) := by
  calc
    runFast 60000 (some (8025054,187249)) = runFast 10000 (runFast 50000 (some (8025054,187249))) := runFast_add 50000 10000 _
    _ = _ := by rw [prefix4,seg5]
private theorem prefix6 : runFast 70000 (some (8025054,187249)) = some (273203,4309493) := by
  calc
    runFast 70000 (some (8025054,187249)) = runFast 10000 (runFast 60000 (some (8025054,187249))) := runFast_add 60000 10000 _
    _ = _ := by rw [prefix5,seg6]
private theorem prefix7 : runFast 80000 (some (8025054,187249)) = some (8723202,119714) := by
  calc
    runFast 80000 (some (8025054,187249)) = runFast 10000 (runFast 70000 (some (8025054,187249))) := runFast_add 70000 10000 _
    _ = _ := by rw [prefix6,seg7]
private theorem prefix8 : runFast 90000 (some (8025054,187249)) = some (7400772,816268) := by
  calc
    runFast 90000 (some (8025054,187249)) = runFast 10000 (runFast 80000 (some (8025054,187249))) := runFast_add 80000 10000 _
    _ = _ := by rw [prefix7,seg8]
private theorem prefix9 : runFast 100000 (some (8025054,187249)) = some (8899188,102006) := by
  calc
    runFast 100000 (some (8025054,187249)) = runFast 10000 (runFast 90000 (some (8025054,187249))) := runFast_add 90000 10000 _
    _ = _ := by rw [prefix8,seg9]
private theorem prefix10 : runFast 110000 (some (8025054,187249)) = some (4907210,2132497) := by
  calc
    runFast 110000 (some (8025054,187249)) = runFast 10000 (runFast 100000 (some (8025054,187249))) := runFast_add 100000 10000 _
    _ = _ := by rw [prefix9,seg10]
private theorem prefix11 : runFast 120000 (some (8025054,187249)) = some (7547038,847658) := by
  calc
    runFast 120000 (some (8025054,187249)) = runFast 10000 (runFast 110000 (some (8025054,187249))) := runFast_add 110000 10000 _
    _ = _ := by rw [prefix10,seg11]
private theorem prefix12 : runFast 130000 (some (8025054,187249)) = some (4961225,2175614) := by
  calc
    runFast 130000 (some (8025054,187249)) = runFast 10000 (runFast 120000 (some (8025054,187249))) := runFast_add 120000 10000 _
    _ = _ := by rw [prefix11,seg12]
private theorem prefix13 : runFast 140000 (some (8025054,187249)) = some (627231,4377830) := by
  calc
    runFast 140000 (some (8025054,187249)) = runFast 10000 (runFast 130000 (some (8025054,187249))) := runFast_add 130000 10000 _
    _ = _ := by rw [prefix12,seg13]
private theorem prefix14 : runFast 150000 (some (8025054,187249)) = some (7099237,1176830) := by
  calc
    runFast 150000 (some (8025054,187249)) = runFast 10000 (runFast 140000 (some (8025054,187249))) := runFast_add 140000 10000 _
    _ = _ := by rw [prefix13,seg14]

theorem part7 : runFast 150000 (some (8025054,187249)) = some (7099237,1176830) := prefix14
#print axioms part7
end BB6.Agent12TerminalCutoff
