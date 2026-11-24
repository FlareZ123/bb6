import M8TraceBridge

set_option maxRecDepth 300000
set_option maxHeartbeats 0
namespace BB6.Agent12TerminalCutoff
open BB6.Agent1M8

private theorem seg0 : runFast 10000 (some (7099237,1176830)) = some (3406844,3058532) := by decide +kernel
private theorem seg1 : runFast 10000 (some (3406844,3058532)) = some (5470759,2061513) := by decide +kernel
private theorem seg2 : runFast 10000 (some (5470759,2061513)) = some (1245032,4209459) := by decide +kernel
private theorem seg3 : runFast 10000 (some (1245032,4209459)) = some (7030420,1351876) := by decide +kernel
private theorem seg4 : runFast 10000 (some (7030420,1351876)) = some (2167807,3818304) := by decide +kernel
private theorem seg5 : runFast 10000 (some (2167807,3818304)) = some (8012382,930850) := by decide +kernel
private theorem seg6 : runFast 10000 (some (8012382,930850)) = some (3845290,3049765) := by decide +kernel
private theorem seg7 : runFast 10000 (some (3845290,3049765)) = some (6629311,1692768) := by decide +kernel
private theorem seg8 : runFast 10000 (some (6629311,1692768)) = some (4698821,2692842) := by decide +kernel
private theorem seg9 : runFast 10000 (some (4698821,2692842)) = some (8488198,832744) := by decide +kernel
private theorem seg10 : runFast 10000 (some (8488198,832744)) = some (2684479,3769968) := by decide +kernel
private theorem seg11 : runFast 10000 (some (2684479,3769968)) = some (4645466,2824557) := by decide +kernel
private theorem seg12 : runFast 10000 (some (4645466,2824557)) = some (9264187,550045) := by decide +kernel
private theorem seg13 : runFast 10000 (some (9264187,550045)) = some (4180095,3127121) := by decide +kernel
private theorem seg14 : runFast 10000 (some (4180095,3127121)) = some (3780428,3362298) := by decide +kernel

private theorem prefix0 : runFast 10000 (some (7099237,1176830)) = some (3406844,3058532) := seg0
private theorem prefix1 : runFast 20000 (some (7099237,1176830)) = some (5470759,2061513) := by
  calc
    runFast 20000 (some (7099237,1176830)) = runFast 10000 (runFast 10000 (some (7099237,1176830))) := runFast_add 10000 10000 _
    _ = _ := by rw [prefix0,seg1]
private theorem prefix2 : runFast 30000 (some (7099237,1176830)) = some (1245032,4209459) := by
  calc
    runFast 30000 (some (7099237,1176830)) = runFast 10000 (runFast 20000 (some (7099237,1176830))) := runFast_add 20000 10000 _
    _ = _ := by rw [prefix1,seg2]
private theorem prefix3 : runFast 40000 (some (7099237,1176830)) = some (7030420,1351876) := by
  calc
    runFast 40000 (some (7099237,1176830)) = runFast 10000 (runFast 30000 (some (7099237,1176830))) := runFast_add 30000 10000 _
    _ = _ := by rw [prefix2,seg3]
private theorem prefix4 : runFast 50000 (some (7099237,1176830)) = some (2167807,3818304) := by
  calc
    runFast 50000 (some (7099237,1176830)) = runFast 10000 (runFast 40000 (some (7099237,1176830))) := runFast_add 40000 10000 _
    _ = _ := by rw [prefix3,seg4]
private theorem prefix5 : runFast 60000 (some (7099237,1176830)) = some (8012382,930850) := by
  calc
    runFast 60000 (some (7099237,1176830)) = runFast 10000 (runFast 50000 (some (7099237,1176830))) := runFast_add 50000 10000 _
    _ = _ := by rw [prefix4,seg5]
private theorem prefix6 : runFast 70000 (some (7099237,1176830)) = some (3845290,3049765) := by
  calc
    runFast 70000 (some (7099237,1176830)) = runFast 10000 (runFast 60000 (some (7099237,1176830))) := runFast_add 60000 10000 _
    _ = _ := by rw [prefix5,seg6]
private theorem prefix7 : runFast 80000 (some (7099237,1176830)) = some (6629311,1692768) := by
  calc
    runFast 80000 (some (7099237,1176830)) = runFast 10000 (runFast 70000 (some (7099237,1176830))) := runFast_add 70000 10000 _
    _ = _ := by rw [prefix6,seg7]
private theorem prefix8 : runFast 90000 (some (7099237,1176830)) = some (4698821,2692842) := by
  calc
    runFast 90000 (some (7099237,1176830)) = runFast 10000 (runFast 80000 (some (7099237,1176830))) := runFast_add 80000 10000 _
    _ = _ := by rw [prefix7,seg8]
private theorem prefix9 : runFast 100000 (some (7099237,1176830)) = some (8488198,832744) := by
  calc
    runFast 100000 (some (7099237,1176830)) = runFast 10000 (runFast 90000 (some (7099237,1176830))) := runFast_add 90000 10000 _
    _ = _ := by rw [prefix8,seg9]
private theorem prefix10 : runFast 110000 (some (7099237,1176830)) = some (2684479,3769968) := by
  calc
    runFast 110000 (some (7099237,1176830)) = runFast 10000 (runFast 100000 (some (7099237,1176830))) := runFast_add 100000 10000 _
    _ = _ := by rw [prefix9,seg10]
private theorem prefix11 : runFast 120000 (some (7099237,1176830)) = some (4645466,2824557) := by
  calc
    runFast 120000 (some (7099237,1176830)) = runFast 10000 (runFast 110000 (some (7099237,1176830))) := runFast_add 110000 10000 _
    _ = _ := by rw [prefix10,seg11]
private theorem prefix12 : runFast 130000 (some (7099237,1176830)) = some (9264187,550045) := by
  calc
    runFast 130000 (some (7099237,1176830)) = runFast 10000 (runFast 120000 (some (7099237,1176830))) := runFast_add 120000 10000 _
    _ = _ := by rw [prefix11,seg12]
private theorem prefix13 : runFast 140000 (some (7099237,1176830)) = some (4180095,3127121) := by
  calc
    runFast 140000 (some (7099237,1176830)) = runFast 10000 (runFast 130000 (some (7099237,1176830))) := runFast_add 130000 10000 _
    _ = _ := by rw [prefix12,seg13]
private theorem prefix14 : runFast 150000 (some (7099237,1176830)) = some (3780428,3362298) := by
  calc
    runFast 150000 (some (7099237,1176830)) = runFast 10000 (runFast 140000 (some (7099237,1176830))) := runFast_add 140000 10000 _
    _ = _ := by rw [prefix13,seg14]

theorem part8 : runFast 150000 (some (7099237,1176830)) = some (3780428,3362298) := prefix14
#print axioms part8
end BB6.Agent12TerminalCutoff
