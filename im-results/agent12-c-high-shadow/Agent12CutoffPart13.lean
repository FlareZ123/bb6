import M8TraceBridge

set_option maxRecDepth 300000
set_option maxHeartbeats 0
namespace BB6.Agent12TerminalCutoff
open BB6.Agent1M8

private theorem seg0 : runFast 10000 (some (3090118,5806249)) = some (9577031,2597698) := by decide +kernel
private theorem seg1 : runFast 10000 (some (9577031,2597698)) = some (3544285,5648867) := by decide +kernel
private theorem seg2 : runFast 10000 (some (3544285,5648867)) = some (14697381,107124) := by decide +kernel
private theorem seg3 : runFast 10000 (some (14697381,107124)) = some (5118804,4931414) := by decide +kernel
private theorem seg4 : runFast 10000 (some (5118804,4931414)) = some (3387415,5832293) := by decide +kernel
private theorem seg5 : runFast 10000 (some (3387415,5832293)) = some (14618075,252176) := by decide +kernel
private theorem seg6 : runFast 10000 (some (14618075,252176)) = some (10126167,2533193) := by decide +kernel
private theorem seg7 : runFast 10000 (some (10126167,2533193)) = some (13441238,910665) := by decide +kernel
private theorem seg8 : runFast 10000 (some (13441238,910665)) = some (1350986,6991037) := by decide +kernel
private theorem seg9 : runFast 10000 (some (1350986,6991037)) = some (14921070,240977) := by decide +kernel
private theorem seg10 : runFast 10000 (some (14921070,240977)) = some (11558508,1957267) := by decide +kernel
private theorem seg11 : runFast 10000 (some (11558508,1957267)) = some (14751281,395663) := by decide +kernel
private theorem seg12 : runFast 10000 (some (14751281,395663)) = some (13020059,1296388) := by decide +kernel
private theorem seg13 : runFast 10000 (some (13020059,1296388)) = some (5092391,5295321) := by decide +kernel
private theorem seg14 : runFast 10000 (some (5092391,5295321)) = some (14606298,573141) := by decide +kernel

private theorem prefix0 : runFast 10000 (some (3090118,5806249)) = some (9577031,2597698) := seg0
private theorem prefix1 : runFast 20000 (some (3090118,5806249)) = some (3544285,5648867) := by
  calc
    runFast 20000 (some (3090118,5806249)) = runFast 10000 (runFast 10000 (some (3090118,5806249))) := runFast_add 10000 10000 _
    _ = _ := by rw [prefix0,seg1]
private theorem prefix2 : runFast 30000 (some (3090118,5806249)) = some (14697381,107124) := by
  calc
    runFast 30000 (some (3090118,5806249)) = runFast 10000 (runFast 20000 (some (3090118,5806249))) := runFast_add 20000 10000 _
    _ = _ := by rw [prefix1,seg2]
private theorem prefix3 : runFast 40000 (some (3090118,5806249)) = some (5118804,4931414) := by
  calc
    runFast 40000 (some (3090118,5806249)) = runFast 10000 (runFast 30000 (some (3090118,5806249))) := runFast_add 30000 10000 _
    _ = _ := by rw [prefix2,seg3]
private theorem prefix4 : runFast 50000 (some (3090118,5806249)) = some (3387415,5832293) := by
  calc
    runFast 50000 (some (3090118,5806249)) = runFast 10000 (runFast 40000 (some (3090118,5806249))) := runFast_add 40000 10000 _
    _ = _ := by rw [prefix3,seg4]
private theorem prefix5 : runFast 60000 (some (3090118,5806249)) = some (14618075,252176) := by
  calc
    runFast 60000 (some (3090118,5806249)) = runFast 10000 (runFast 50000 (some (3090118,5806249))) := runFast_add 50000 10000 _
    _ = _ := by rw [prefix4,seg5]
private theorem prefix6 : runFast 70000 (some (3090118,5806249)) = some (10126167,2533193) := by
  calc
    runFast 70000 (some (3090118,5806249)) = runFast 10000 (runFast 60000 (some (3090118,5806249))) := runFast_add 60000 10000 _
    _ = _ := by rw [prefix5,seg6]
private theorem prefix7 : runFast 80000 (some (3090118,5806249)) = some (13441238,910665) := by
  calc
    runFast 80000 (some (3090118,5806249)) = runFast 10000 (runFast 70000 (some (3090118,5806249))) := runFast_add 70000 10000 _
    _ = _ := by rw [prefix6,seg7]
private theorem prefix8 : runFast 90000 (some (3090118,5806249)) = some (1350986,6991037) := by
  calc
    runFast 90000 (some (3090118,5806249)) = runFast 10000 (runFast 80000 (some (3090118,5806249))) := runFast_add 80000 10000 _
    _ = _ := by rw [prefix7,seg8]
private theorem prefix9 : runFast 100000 (some (3090118,5806249)) = some (14921070,240977) := by
  calc
    runFast 100000 (some (3090118,5806249)) = runFast 10000 (runFast 90000 (some (3090118,5806249))) := runFast_add 90000 10000 _
    _ = _ := by rw [prefix8,seg9]
private theorem prefix10 : runFast 110000 (some (3090118,5806249)) = some (11558508,1957267) := by
  calc
    runFast 110000 (some (3090118,5806249)) = runFast 10000 (runFast 100000 (some (3090118,5806249))) := runFast_add 100000 10000 _
    _ = _ := by rw [prefix9,seg10]
private theorem prefix11 : runFast 120000 (some (3090118,5806249)) = some (14751281,395663) := by
  calc
    runFast 120000 (some (3090118,5806249)) = runFast 10000 (runFast 110000 (some (3090118,5806249))) := runFast_add 110000 10000 _
    _ = _ := by rw [prefix10,seg11]
private theorem prefix12 : runFast 130000 (some (3090118,5806249)) = some (13020059,1296388) := by
  calc
    runFast 130000 (some (3090118,5806249)) = runFast 10000 (runFast 120000 (some (3090118,5806249))) := runFast_add 120000 10000 _
    _ = _ := by rw [prefix11,seg12]
private theorem prefix13 : runFast 140000 (some (3090118,5806249)) = some (5092391,5295321) := by
  calc
    runFast 140000 (some (3090118,5806249)) = runFast 10000 (runFast 130000 (some (3090118,5806249))) := runFast_add 130000 10000 _
    _ = _ := by rw [prefix12,seg13]
private theorem prefix14 : runFast 150000 (some (3090118,5806249)) = some (14606298,573141) := by
  calc
    runFast 150000 (some (3090118,5806249)) = runFast 10000 (runFast 140000 (some (3090118,5806249))) := runFast_add 140000 10000 _
    _ = _ := by rw [prefix13,seg14]

theorem part13 : runFast 150000 (some (3090118,5806249)) = some (14606298,573141) := prefix14
#print axioms part13
end BB6.Agent12TerminalCutoff
