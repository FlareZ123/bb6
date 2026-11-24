import M8TraceBridge

set_option maxRecDepth 300000
set_option maxHeartbeats 0
namespace BB6.Agent12TerminalCutoff
open BB6.Agent1M8

private theorem seg0 : runFast 10000 (some (8140864,2231926)) = some (9717863,1478425) := by decide +kernel
private theorem seg1 : runFast 10000 (some (9717863,1478425)) = some (5944870,3399998) := by decide +kernel
private theorem seg2 : runFast 10000 (some (5944870,3399998)) = some (8226298,2293918) := by decide +kernel
private theorem seg3 : runFast 10000 (some (8226298,2293918)) = some (5181795,3851405) := by decide +kernel
private theorem seg4 : runFast 10000 (some (5181795,3851405)) = some (5059843,3947228) := by decide +kernel
private theorem seg5 : runFast 10000 (some (5059843,3947228)) = some (7809412,2607019) := by decide +kernel
private theorem seg6 : runFast 10000 (some (7809412,2607019)) = some (8762282,2165440) := by decide +kernel
private theorem seg7 : runFast 10000 (some (8762282,2165440)) = some (5032463,4065681) := by decide +kernel
private theorem seg8 : runFast 10000 (some (5032463,4065681)) = some (993865,6120172) := by decide +kernel
private theorem seg9 : runFast 10000 (some (993865,6120172)) = some (12535996,384159) := by decide +kernel
private theorem seg10 : runFast 10000 (some (12535996,384159)) = some (1409593,5982254) := by decide +kernel
private theorem seg11 : runFast 10000 (some (1409593,5982254)) = some (6805101,3319098) := by decide +kernel
private theorem seg12 : runFast 10000 (some (6805101,3319098)) = some (2722966,5395041) := by decide +kernel
private theorem seg13 : runFast 10000 (some (2722966,5395041)) = some (6324417,3629530) := by decide +kernel
private theorem seg14 : runFast 10000 (some (6324417,3629530)) = some (2816828,5418179) := by decide +kernel

private theorem prefix0 : runFast 10000 (some (8140864,2231926)) = some (9717863,1478425) := seg0
private theorem prefix1 : runFast 20000 (some (8140864,2231926)) = some (5944870,3399998) := by
  calc
    runFast 20000 (some (8140864,2231926)) = runFast 10000 (runFast 10000 (some (8140864,2231926))) := runFast_add 10000 10000 _
    _ = _ := by rw [prefix0,seg1]
private theorem prefix2 : runFast 30000 (some (8140864,2231926)) = some (8226298,2293918) := by
  calc
    runFast 30000 (some (8140864,2231926)) = runFast 10000 (runFast 20000 (some (8140864,2231926))) := runFast_add 20000 10000 _
    _ = _ := by rw [prefix1,seg2]
private theorem prefix3 : runFast 40000 (some (8140864,2231926)) = some (5181795,3851405) := by
  calc
    runFast 40000 (some (8140864,2231926)) = runFast 10000 (runFast 30000 (some (8140864,2231926))) := runFast_add 30000 10000 _
    _ = _ := by rw [prefix2,seg3]
private theorem prefix4 : runFast 50000 (some (8140864,2231926)) = some (5059843,3947228) := by
  calc
    runFast 50000 (some (8140864,2231926)) = runFast 10000 (runFast 40000 (some (8140864,2231926))) := runFast_add 40000 10000 _
    _ = _ := by rw [prefix3,seg4]
private theorem prefix5 : runFast 60000 (some (8140864,2231926)) = some (7809412,2607019) := by
  calc
    runFast 60000 (some (8140864,2231926)) = runFast 10000 (runFast 50000 (some (8140864,2231926))) := runFast_add 50000 10000 _
    _ = _ := by rw [prefix4,seg5]
private theorem prefix6 : runFast 70000 (some (8140864,2231926)) = some (8762282,2165440) := by
  calc
    runFast 70000 (some (8140864,2231926)) = runFast 10000 (runFast 60000 (some (8140864,2231926))) := runFast_add 60000 10000 _
    _ = _ := by rw [prefix5,seg6]
private theorem prefix7 : runFast 80000 (some (8140864,2231926)) = some (5032463,4065681) := by
  calc
    runFast 80000 (some (8140864,2231926)) = runFast 10000 (runFast 70000 (some (8140864,2231926))) := runFast_add 70000 10000 _
    _ = _ := by rw [prefix6,seg7]
private theorem prefix8 : runFast 90000 (some (8140864,2231926)) = some (993865,6120172) := by
  calc
    runFast 90000 (some (8140864,2231926)) = runFast 10000 (runFast 80000 (some (8140864,2231926))) := runFast_add 80000 10000 _
    _ = _ := by rw [prefix7,seg8]
private theorem prefix9 : runFast 100000 (some (8140864,2231926)) = some (12535996,384159) := by
  calc
    runFast 100000 (some (8140864,2231926)) = runFast 10000 (runFast 90000 (some (8140864,2231926))) := runFast_add 90000 10000 _
    _ = _ := by rw [prefix8,seg9]
private theorem prefix10 : runFast 110000 (some (8140864,2231926)) = some (1409593,5982254) := by
  calc
    runFast 110000 (some (8140864,2231926)) = runFast 10000 (runFast 100000 (some (8140864,2231926))) := runFast_add 100000 10000 _
    _ = _ := by rw [prefix9,seg10]
private theorem prefix11 : runFast 120000 (some (8140864,2231926)) = some (6805101,3319098) := by
  calc
    runFast 120000 (some (8140864,2231926)) = runFast 10000 (runFast 110000 (some (8140864,2231926))) := runFast_add 110000 10000 _
    _ = _ := by rw [prefix10,seg11]
private theorem prefix12 : runFast 130000 (some (8140864,2231926)) = some (2722966,5395041) := by
  calc
    runFast 130000 (some (8140864,2231926)) = runFast 10000 (runFast 120000 (some (8140864,2231926))) := runFast_add 120000 10000 _
    _ = _ := by rw [prefix11,seg12]
private theorem prefix13 : runFast 140000 (some (8140864,2231926)) = some (6324417,3629530) := by
  calc
    runFast 140000 (some (8140864,2231926)) = runFast 10000 (runFast 130000 (some (8140864,2231926))) := runFast_add 130000 10000 _
    _ = _ := by rw [prefix12,seg13]
private theorem prefix14 : runFast 150000 (some (8140864,2231926)) = some (2816828,5418179) := by
  calc
    runFast 150000 (some (8140864,2231926)) = runFast 10000 (runFast 140000 (some (8140864,2231926))) := runFast_add 140000 10000 _
    _ = _ := by rw [prefix13,seg14]

theorem part11 : runFast 150000 (some (8140864,2231926)) = some (2816828,5418179) := prefix14
#print axioms part11
end BB6.Agent12TerminalCutoff
