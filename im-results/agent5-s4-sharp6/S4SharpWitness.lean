import S4Toggle
import Lean.Elab.Tactic.Omega

/-! Explicit source-map synthetic stopping completions at the 68 six-digit
    prefix-cycle phases omitted by the existing mod-64 sufficient sieve.
    No claim of actual blank-root reachability is made. -/
namespace S4Sharp6
open S4Power S4Octet S4Toggle
set_option maxHeartbeats 0
set_option maxRecDepth 10000

/-- Phase 14, synthetic suffix 2106; failure at G 219. -/
theorem bad_0014 : P [283,908,2493,4081,13917,3757,2106] = none := by
  have h0 : G 509 [283,908,2493,4081,13917,3757,2106] = some [398,1304,2493,4081,13917,3757,2106] := by simp [G,H]
  have h1 : G 290 [398,1304,2493,4081,13917,3757,2106] = some [346,1648,2493,4081,13917,3757,2106] := by simp [G,H]
  have hg : G 219 [346,1648,2493,4081,13917,3757,2106] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 23, synthetic suffix 6696; failure at G 509. -/
theorem bad_0023 : P [282,967,2129,1857,9553,13780,6696] = none := by
  have hg : G 509 [282,967,2129,1857,9553,13780,6696] = none :=
    (G_none_iff_power 509 _ (by omega)).mpr ⟨20, by decide⟩
  simp [P,hg]

/-- Phase 33, synthetic suffix 2070; failure at G 290. -/
theorem bad_0033 : P [281,512,1339,6000,7805,6592,2070] = none := by
  have h0 : G 509 [281,512,1339,6000,7805,6592,2070] = some [397,907,1339,6000,7805,6592,2070] := by simp [G,H]
  have hg : G 290 [397,907,1339,6000,7805,6592,2070] = none :=
    (G_none_iff_power 290 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,h0,hg]

/-- Phase 34, synthetic suffix 3160; failure at G 219. -/
theorem bad_0034 : P [283,906,982,3491,5648,6120,3160] = none := by
  have h0 : G 509 [283,906,982,3491,5648,6120,3160] = some [398,1302,982,3491,5648,6120,3160] := by simp [G,H]
  have h1 : G 290 [398,1302,982,3491,5648,6120,3160] = some [346,1646,982,3491,5648,6120,3160] := by simp [G,H]
  have hg : G 219 [346,1646,982,3491,5648,6120,3160] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 36, synthetic suffix 3755; failure at G 219. -/
theorem bad_0036 : P [280,396,743,4056,3940,5030,3755] = none := by
  have h0 : G 509 [280,396,743,4056,3940,5030,3755] = some [394,395,569,2315,6253,5030,3755] := by simp [G,H]
  have h1 : G 290 [394,395,569,2315,6253,5030,3755] = some [344,737,569,2315,6253,5030,3755] := by simp [G,H]
  have hg : G 219 [344,737,569,2315,6253,5030,3755] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 63, synthetic suffix 2125; failure at G 509. -/
theorem bad_0063 : P [282,965,1732,7418,3642,8153,2125] = none := by
  have hg : G 509 [282,965,1732,7418,3642,8153,2125] = none :=
    (G_none_iff_power 509 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,hg]

/-- Phase 98, synthetic suffix 1962; failure at G 219. -/
theorem bad_0098 : P [283,906,982,3491,5652,24898,1962] = none := by
  have h0 : G 509 [283,906,982,3491,5652,24898,1962] = some [398,1302,982,3491,5652,24898,1962] := by simp [G,H]
  have h1 : G 290 [398,1302,982,3491,5652,24898,1962] = some [346,1646,982,3491,5652,24898,1962] := by simp [G,H]
  have hg : G 219 [346,1646,982,3491,5652,24898,1962] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨20, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 142, synthetic suffix 5077; failure at G 219. -/
theorem bad_0142 : P [283,908,2493,4081,13921,14197,5077] = none := by
  have h0 : G 509 [283,908,2493,4081,13921,14197,5077] = some [398,1304,2493,4081,13921,14197,5077] := by simp [G,H]
  have h1 : G 290 [398,1304,2493,4081,13921,14197,5077] = some [346,1648,2493,4081,13921,14197,5077] := by simp [G,H]
  have hg : G 219 [346,1648,2493,4081,13921,14197,5077] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨20, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 161, synthetic suffix 15896; failure at G 290. -/
theorem bad_0161 : P [281,512,1339,6000,7809,28090,15896] = none := by
  have h0 : G 509 [281,512,1339,6000,7809,28090,15896] = some [397,907,1339,6000,7809,28090,15896] := by simp [G,H]
  have hg : G 290 [397,907,1339,6000,7809,28090,15896] = none :=
    (G_none_iff_power 290 _ (by omega)).mpr ⟨21, by decide⟩
  simp [P,h0,hg]

/-- Phase 167, synthetic suffix 7798; failure at G 219. -/
theorem bad_0167 : P [282,967,2128,1427,3843,14249,7798] = none := by
  have h0 : G 509 [282,967,2128,1427,3843,14249,7798] = some [395,681,1407,2832,3843,14249,7798] := by simp [G,H]
  have h1 : G 290 [395,681,1407,2832,3843,14249,7798] = some [342,514,1919,2832,3843,14249,7798] := by simp [G,H]
  have hg : G 219 [342,514,1919,2832,3843,14249,7798] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨20, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 191, synthetic suffix 54; failure at G 509. -/
theorem bad_0191 : P [282,965,1732,7418,3644,12294,54] = none := by
  have hg : G 509 [282,965,1732,7418,3644,12294,54] = none :=
    (G_none_iff_power 509 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,hg]

/-- Phase 193, synthetic suffix 2255; failure at G 290. -/
theorem bad_0193 : P [281,512,1339,5998,3978,8136,2255] = none := by
  have h0 : G 509 [281,512,1339,5998,3978,8136,2255] = some [397,907,1339,5998,3978,8136,2255] := by simp [G,H]
  have hg : G 290 [397,907,1339,5998,3978,8136,2255] = none :=
    (G_none_iff_power 290 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,h0,hg]

/-- Phase 211, synthetic suffix 5360; failure at G 290. -/
theorem bad_0211 : P [282,964,974,2637,13534,14347,5360] = none := by
  have h0 : G 509 [282,964,974,2637,13534,14347,5360] = some [395,682,1654,2637,13534,14347,5360] := by simp [G,H]
  have hg : G 290 [395,682,1654,2637,13534,14347,5360] = none :=
    (G_none_iff_power 290 _ (by omega)).mpr ⟨20, by decide⟩
  simp [P,h0,hg]

/-- Phase 215, synthetic suffix 6328; failure at G 219. -/
theorem bad_0215 : P [282,967,2129,1857,9552,11022,6328] = none := by
  have h0 : G 509 [282,967,2129,1857,9552,11022,6328] = some [395,681,1405,1631,5594,16614,6328] := by simp [G,H]
  have h1 : G 290 [395,681,1405,1631,5594,16614,6328] = some [342,514,1917,1631,5594,16614,6328] := by simp [G,H]
  have hg : G 219 [342,514,1917,1631,5594,16614,6328] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨20, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 242, synthetic suffix 3569; failure at G 219. -/
theorem bad_0242 : P [283,906,984,4292,3251,6300,3569] = none := by
  have h0 : G 509 [283,906,984,4292,3251,6300,3569] = some [398,1302,984,4292,3251,6300,3569] := by simp [G,H]
  have h1 : G 290 [398,1302,984,4292,3251,6300,3569] = some [346,1646,984,4292,3251,6300,3569] := by simp [G,H]
  have hg : G 219 [346,1646,984,4292,3251,6300,3569] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 270, synthetic suffix 2105; failure at G 219. -/
theorem bad_0270 : P [283,908,2493,4081,13917,3759,2105] = none := by
  have h0 : G 509 [283,908,2493,4081,13917,3759,2105] = some [398,1304,2493,4081,13917,3759,2105] := by simp [G,H]
  have h1 : G 290 [398,1304,2493,4081,13917,3759,2105] = some [346,1648,2493,4081,13917,3759,2105] := by simp [G,H]
  have hg : G 219 [346,1648,2493,4081,13917,3759,2105] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 279, synthetic suffix 104; failure at G 219. -/
theorem bad_0279 : P [282,967,2129,1857,9553,13781,104] = none := by
  have h0 : G 509 [282,967,2129,1857,9553,13781,104] = some [395,681,1405,1631,5592,9689,9791] := by simp [G,H]
  have h1 : G 290 [395,681,1405,1631,5592,9689,9791] = some [342,514,1917,1631,5592,9689,9791] := by simp [G,H]
  have hg : G 219 [342,514,1917,1631,5592,9689,9791] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨20, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 290, synthetic suffix 3159; failure at G 219. -/
theorem bad_0290 : P [283,906,982,3491,5648,6122,3159] = none := by
  have h0 : G 509 [283,906,982,3491,5648,6122,3159] = some [398,1302,982,3491,5648,6122,3159] := by simp [G,H]
  have h1 : G 290 [398,1302,982,3491,5648,6122,3159] = some [346,1646,982,3491,5648,6122,3159] := by simp [G,H]
  have hg : G 219 [346,1646,982,3491,5648,6122,3159] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 303, synthetic suffix 877; failure at G 290. -/
theorem bad_0303 : P [282,965,1729,2904,4020,11374,877] = none := by
  have h0 : G 509 [282,965,1729,2904,4020,11374,877] = some [395,680,1207,4109,4020,11374,877] := by simp [G,H]
  have hg : G 290 [395,680,1207,4109,4020,11374,877] = none :=
    (G_none_iff_power 290 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,h0,hg]

/-- Phase 311, synthetic suffix 40; failure at G 219. -/
theorem bad_0311 : P [282,967,2129,1856,4258,12658,40] = none := by
  have h0 : G 509 [282,967,2129,1856,4258,12658,40] = some [395,681,1405,1633,5889,12658,40] := by simp [G,H]
  have h1 : G 290 [395,681,1405,1633,5889,12658,40] = some [342,514,1917,1633,5889,12658,40] := by simp [G,H]
  have hg : G 219 [342,514,1917,1633,5889,12658,40] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 343, synthetic suffix 630; failure at G 509. -/
theorem bad_0343 : P [282,967,2129,1857,9555,25911,630] = none := by
  have hg : G 509 [282,967,2129,1857,9555,25911,630] = none :=
    (G_none_iff_power 509 _ (by omega)).mpr ⟨20, by decide⟩
  simp [P,hg]

/-- Phase 354, synthetic suffix 1963; failure at G 219. -/
theorem bad_0354 : P [283,906,982,3491,5652,24896,1963] = none := by
  have h0 : G 509 [283,906,982,3491,5652,24896,1963] = some [398,1302,982,3491,5652,24896,1963] := by simp [G,H]
  have h1 : G 290 [398,1302,982,3491,5652,24896,1963] = some [346,1646,982,3491,5652,24896,1963] := by simp [G,H]
  have hg : G 219 [346,1646,982,3491,5652,24896,1963] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨20, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 356, synthetic suffix 7252; failure at G 219. -/
theorem bad_0356 : P [280,396,743,4056,3942,14419,7252] = none := by
  have h0 : G 509 [280,396,743,4056,3942,14419,7252] = some [394,395,569,2315,6255,14419,7252] := by simp [G,H]
  have h1 : G 290 [394,395,569,2315,6255,14419,7252] = some [344,737,569,2315,6255,14419,7252] := by simp [G,H]
  have hg : G 219 [344,737,569,2315,6255,14419,7252] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨20, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 359, synthetic suffix 2166; failure at G 219. -/
theorem bad_0359 : P [282,967,2128,1427,3841,9130,2166] = none := by
  have h0 : G 509 [282,967,2128,1427,3841,9130,2166] = some [395,681,1407,2832,3841,9130,2166] := by simp [G,H]
  have h1 : G 290 [395,681,1407,2832,3841,9130,2166] = some [342,514,1919,2832,3841,9130,2166] := by simp [G,H]
  have hg : G 219 [342,514,1919,2832,3841,9130,2166] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 417, synthetic suffix 15895; failure at G 290. -/
theorem bad_0417 : P [281,512,1339,6000,7809,28092,15895] = none := by
  have h0 : G 509 [281,512,1339,6000,7809,28092,15895] = some [397,907,1339,6000,7809,28092,15895] := by simp [G,H]
  have hg : G 290 [397,907,1339,6000,7809,28092,15895] = none :=
    (G_none_iff_power 290 _ (by omega)).mpr ⟨21, by decide⟩
  simp [P,h0,hg]

/-- Phase 418, synthetic suffix 5976; failure at G 219. -/
theorem bad_0418 : P [283,906,982,3491,5650,16871,5976] = none := by
  have h0 : G 509 [283,906,982,3491,5650,16871,5976] = some [398,1302,982,3491,5650,16871,5976] := by simp [G,H]
  have h1 : G 290 [398,1302,982,3491,5650,16871,5976] = some [346,1646,982,3491,5650,16871,5976] := by simp [G,H]
  have hg : G 219 [346,1646,982,3491,5650,16871,5976] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨20, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 423, synthetic suffix 7799; failure at G 219. -/
theorem bad_0423 : P [282,967,2128,1427,3843,14247,7799] = none := by
  have h0 : G 509 [282,967,2128,1427,3843,14247,7799] = some [395,681,1407,2832,3843,14247,7799] := by simp [G,H]
  have h1 : G 290 [395,681,1407,2832,3843,14247,7799] = some [342,514,1919,2832,3843,14247,7799] := by simp [G,H]
  have hg : G 219 [342,514,1919,2832,3843,14247,7799] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨20, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 430, synthetic suffix 1890; failure at G 219. -/
theorem bad_0430 : P [283,908,2493,4079,5130,8583,1890] = none := by
  have h0 : G 509 [283,908,2493,4079,5130,8583,1890] = some [398,1304,2493,4079,5130,8583,1890] := by simp [G,H]
  have h1 : G 290 [398,1304,2493,4079,5130,8583,1890] = some [346,1648,2493,4079,5130,8583,1890] := by simp [G,H]
  have hg : G 219 [346,1648,2493,4079,5130,8583,1890] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 434, synthetic suffix 1943; failure at G 219. -/
theorem bad_0434 : P [283,906,984,4292,3253,9551,1943] = none := by
  have h0 : G 509 [283,906,984,4292,3253,9551,1943] = some [398,1302,984,4292,3253,9551,1943] := by simp [G,H]
  have h1 : G 290 [398,1302,984,4292,3253,9551,1943] = some [346,1646,984,4292,3253,9551,1943] := by simp [G,H]
  have hg : G 219 [346,1646,984,4292,3253,9551,1943] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 447, synthetic suffix 56; failure at G 509. -/
theorem bad_0447 : P [282,965,1732,7418,3644,12290,56] = none := by
  have hg : G 509 [282,965,1732,7418,3644,12290,56] = none :=
    (G_none_iff_power 509 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,hg]

/-- Phase 449, synthetic suffix 2256; failure at G 290. -/
theorem bad_0449 : P [281,512,1339,5998,3978,8134,2256] = none := by
  have h0 : G 509 [281,512,1339,5998,3978,8134,2256] = some [397,907,1339,5998,3978,8134,2256] := by simp [G,H]
  have hg : G 290 [397,907,1339,5998,3978,8134,2256] = none :=
    (G_none_iff_power 290 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,h0,hg]

/-- Phase 471, synthetic suffix 6327; failure at G 219. -/
theorem bad_0471 : P [282,967,2129,1857,9552,11024,6327] = none := by
  have h0 : G 509 [282,967,2129,1857,9552,11024,6327] = some [395,681,1405,1631,5594,16616,6327] := by simp [G,H]
  have h1 : G 290 [395,681,1405,1631,5594,16616,6327] = some [342,514,1917,1631,5594,16616,6327] := by simp [G,H]
  have hg : G 219 [342,514,1917,1631,5594,16616,6327] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨20, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 484, synthetic suffix 4638; failure at G 219. -/
theorem bad_0484 : P [280,396,743,4056,3944,19646,4638] = none := by
  have h0 : G 509 [280,396,743,4056,3944,19646,4638] = some [394,395,569,2315,6257,19646,4638] := by simp [G,H]
  have h1 : G 290 [394,395,569,2315,6257,19646,4638] = some [344,737,569,2315,6257,19646,4638] := by simp [G,H]
  have hg : G 219 [344,737,569,2315,6257,19646,4638] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨20, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 495, synthetic suffix 1893; failure at G 290. -/
theorem bad_0495 : P [282,965,1729,2904,4018,9343,1893] = none := by
  have h0 : G 509 [282,965,1729,2904,4018,9343,1893] = some [395,680,1207,4109,4018,9343,1893] := by simp [G,H]
  have hg : G 290 [395,680,1207,4109,4018,9343,1893] = none :=
    (G_none_iff_power 290 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,h0,hg]

/-- Phase 499, synthetic suffix 583; failure at G 290. -/
theorem bad_0499 : P [282,964,974,2633,2942,4622,583] = none := by
  have h0 : G 509 [282,964,974,2633,2942,4622,583] = some [395,682,1654,2633,2942,4622,583] := by simp [G,H]
  have hg : G 290 [395,682,1654,2633,2942,4622,583] = none :=
    (G_none_iff_power 290 _ (by omega)).mpr ⟨18, by decide⟩
  simp [P,h0,hg]

/-- Phase 511, synthetic suffix 317; failure at G 509. -/
theorem bad_0511 : P [282,965,1732,7418,3640,3578,317] = none := by
  have hg : G 509 [282,965,1732,7418,3640,3578,317] = none :=
    (G_none_iff_power 509 _ (by omega)).mpr ⟨18, by decide⟩
  simp [P,hg]

/-- Phase 513, synthetic suffix 339; failure at G 290. -/
theorem bad_0513 : P [281,512,1339,5998,3976,3777,339] = none := by
  have h0 : G 509 [281,512,1339,5998,3976,3777,339] = some [397,907,1339,5998,3976,3777,339] := by simp [G,H]
  have hg : G 290 [397,907,1339,5998,3976,3777,339] = none :=
    (G_none_iff_power 290 _ (by omega)).mpr ⟨18, by decide⟩
  simp [P,h0,hg]

/-- Phase 526, synthetic suffix 2107; failure at G 219. -/
theorem bad_0526 : P [283,908,2493,4081,13917,3755,2107] = none := by
  have h0 : G 509 [283,908,2493,4081,13917,3755,2107] = some [398,1304,2493,4081,13917,3755,2107] := by simp [G,H]
  have h1 : G 290 [398,1304,2493,4081,13917,3755,2107] = some [346,1648,2493,4081,13917,3755,2107] := by simp [G,H]
  have hg : G 219 [346,1648,2493,4081,13917,3755,2107] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 548, synthetic suffix 3753; failure at G 219. -/
theorem bad_0548 : P [280,396,743,4056,3940,5034,3753] = none := by
  have h0 : G 509 [280,396,743,4056,3940,5034,3753] = some [394,395,569,2315,6253,5034,3753] := by simp [G,H]
  have h1 : G 290 [394,395,569,2315,6253,5034,3753] = some [344,737,569,2315,6253,5034,3753] := by simp [G,H]
  have hg : G 219 [344,737,569,2315,6253,5034,3753] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 567, synthetic suffix 39; failure at G 219. -/
theorem bad_0567 : P [282,967,2129,1856,4258,12660,39] = none := by
  have h0 : G 509 [282,967,2129,1856,4258,12660,39] = some [395,681,1405,1633,5889,12660,39] := by simp [G,H]
  have h1 : G 290 [395,681,1405,1633,5889,12660,39] = some [342,514,1917,1633,5889,12660,39] := by simp [G,H]
  have hg : G 219 [342,514,1917,1633,5889,12660,39] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 575, synthetic suffix 2126; failure at G 509. -/
theorem bad_0575 : P [282,965,1732,7418,3642,8151,2126] = none := by
  have hg : G 509 [282,965,1732,7418,3642,8151,2126] = none :=
    (G_none_iff_power 509 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,hg]

/-- Phase 599, synthetic suffix 631; failure at G 509. -/
theorem bad_0599 : P [282,967,2129,1857,9555,25909,631] = none := by
  have hg : G 509 [282,967,2129,1857,9555,25909,631] = none :=
    (G_none_iff_power 509 _ (by omega)).mpr ⟨20, by decide⟩
  simp [P,hg]

/-- Phase 612, synthetic suffix 7251; failure at G 219. -/
theorem bad_0612 : P [280,396,743,4056,3942,14421,7251] = none := by
  have h0 : G 509 [280,396,743,4056,3942,14421,7251] = some [394,395,569,2315,6255,14421,7251] := by simp [G,H]
  have h1 : G 290 [394,395,569,2315,6255,14421,7251] = some [344,737,569,2315,6255,14421,7251] := by simp [G,H]
  have hg : G 219 [344,737,569,2315,6255,14421,7251] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨20, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 627, synthetic suffix 7061; failure at G 290. -/
theorem bad_0627 : P [282,964,974,2633,2946,16240,7061] = none := by
  have h0 : G 509 [282,964,974,2633,2946,16240,7061] = some [395,682,1654,2633,2946,16240,7061] := by simp [G,H]
  have hg : G 290 [395,682,1654,2633,2946,16240,7061] = none :=
    (G_none_iff_power 290 _ (by omega)).mpr ⟨20, by decide⟩
  simp [P,h0,hg]

/-- Phase 631, synthetic suffix 1709; failure at G 219. -/
theorem bad_0631 : P [282,967,2129,1856,4256,9321,1709] = none := by
  have h0 : G 509 [282,967,2129,1856,4256,9321,1709] = some [395,681,1405,1633,5887,9321,1709] := by simp [G,H]
  have h1 : G 290 [395,681,1405,1633,5887,9321,1709] = some [342,514,1917,1633,5887,9321,1709] := by simp [G,H]
  have hg : G 219 [342,514,1917,1633,5887,9321,1709] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 654, synthetic suffix 5079; failure at G 219. -/
theorem bad_0654 : P [283,908,2493,4081,13921,14193,5079] = none := by
  have h0 : G 509 [283,908,2493,4081,13921,14193,5079] = some [398,1304,2493,4081,13921,14193,5079] := by simp [G,H]
  have h1 : G 290 [398,1304,2493,4081,13921,14193,5079] = some [346,1648,2493,4081,13921,14193,5079] := by simp [G,H]
  have hg : G 219 [346,1648,2493,4081,13921,14193,5079] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨20, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 673, synthetic suffix 15897; failure at G 290. -/
theorem bad_0673 : P [281,512,1339,6000,7809,28088,15897] = none := by
  have h0 : G 509 [281,512,1339,6000,7809,28088,15897] = some [397,907,1339,6000,7809,28088,15897] := by simp [G,H]
  have hg : G 290 [397,907,1339,6000,7809,28088,15897] = none :=
    (G_none_iff_power 290 _ (by omega)).mpr ⟨21, by decide⟩
  simp [P,h0,hg]

/-- Phase 674, synthetic suffix 5977; failure at G 219. -/
theorem bad_0674 : P [283,906,982,3491,5650,16869,5977] = none := by
  have h0 : G 509 [283,906,982,3491,5650,16869,5977] = some [398,1302,982,3491,5650,16869,5977] := by simp [G,H]
  have h1 : G 290 [398,1302,982,3491,5650,16869,5977] = some [346,1646,982,3491,5650,16869,5977] := by simp [G,H]
  have hg : G 219 [346,1646,982,3491,5650,16869,5977] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨20, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 686, synthetic suffix 1889; failure at G 219. -/
theorem bad_0686 : P [283,908,2493,4079,5130,8585,1889] = none := by
  have h0 : G 509 [283,908,2493,4079,5130,8585,1889] = some [398,1304,2493,4079,5130,8585,1889] := by simp [G,H]
  have h1 : G 290 [398,1304,2493,4079,5130,8585,1889] = some [346,1648,2493,4079,5130,8585,1889] := by simp [G,H]
  have hg : G 219 [346,1648,2493,4079,5130,8585,1889] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 705, synthetic suffix 2254; failure at G 290. -/
theorem bad_0705 : P [281,512,1339,5998,3978,8138,2254] = none := by
  have h0 : G 509 [281,512,1339,5998,3978,8138,2254] = some [397,907,1339,5998,3978,8138,2254] := by simp [G,H]
  have hg : G 290 [397,907,1339,5998,3978,8138,2254] = none :=
    (G_none_iff_power 290 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,h0,hg]

/-- Phase 751, synthetic suffix 1892; failure at G 290. -/
theorem bad_0751 : P [282,965,1729,2904,4018,9345,1892] = none := by
  have h0 : G 509 [282,965,1729,2904,4018,9345,1892] = some [395,680,1207,4109,4018,9345,1892] := by simp [G,H]
  have hg : G 290 [395,680,1207,4109,4018,9345,1892] = none :=
    (G_none_iff_power 290 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,h0,hg]

/-- Phase 754, synthetic suffix 3570; failure at G 219. -/
theorem bad_0754 : P [283,906,984,4292,3251,6298,3570] = none := by
  have h0 : G 509 [283,906,984,4292,3251,6298,3570] = some [398,1302,984,4292,3251,6298,3570] := by simp [G,H]
  have h1 : G 290 [398,1302,984,4292,3251,6298,3570] = some [346,1646,984,4292,3251,6298,3570] := by simp [G,H]
  have hg : G 219 [346,1646,984,4292,3251,6298,3570] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 755, synthetic suffix 584; failure at G 290. -/
theorem bad_0755 : P [282,964,974,2633,2942,4620,584] = none := by
  have h0 : G 509 [282,964,974,2633,2942,4620,584] = some [395,682,1654,2633,2942,4620,584] := by simp [G,H]
  have hg : G 290 [395,682,1654,2633,2942,4620,584] = none :=
    (G_none_iff_power 290 _ (by omega)).mpr ⟨18, by decide⟩
  simp [P,h0,hg]

/-- Phase 759, synthetic suffix 519; failure at G 219. -/
theorem bad_0759 : P [282,967,2129,1856,4254,3510,519] = none := by
  have h0 : G 509 [282,967,2129,1856,4254,3510,519] = some [395,681,1405,1633,5885,3510,519] := by simp [G,H]
  have h1 : G 290 [395,681,1405,1633,5885,3510,519] = some [342,514,1917,1633,5885,3510,519] := by simp [G,H]
  have hg : G 219 [342,514,1917,1633,5885,3510,519] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨18, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 801, synthetic suffix 2069; failure at G 290. -/
theorem bad_0801 : P [281,512,1339,6000,7805,6594,2069] = none := by
  have h0 : G 509 [281,512,1339,6000,7805,6594,2069] = some [397,907,1339,6000,7805,6594,2069] := by simp [G,H]
  have hg : G 290 [397,907,1339,6000,7805,6594,2069] = none :=
    (G_none_iff_power 290 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,h0,hg]

/-- Phase 855, synthetic suffix 629; failure at G 509. -/
theorem bad_0855 : P [282,967,2129,1857,9555,25913,629] = none := by
  have hg : G 509 [282,967,2129,1857,9555,25913,629] = none :=
    (G_none_iff_power 509 _ (by omega)).mpr ⟨20, by decide⟩
  simp [P,hg]

/-- Phase 871, synthetic suffix 2164; failure at G 219. -/
theorem bad_0871 : P [282,967,2128,1427,3841,9134,2164] = none := by
  have h0 : G 509 [282,967,2128,1427,3841,9134,2164] = some [395,681,1407,2832,3841,9134,2164] := by simp [G,H]
  have h1 : G 290 [395,681,1407,2832,3841,9134,2164] = some [342,514,1919,2832,3841,9134,2164] := by simp [G,H]
  have hg : G 219 [342,514,1919,2832,3841,9134,2164] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 887, synthetic suffix 1708; failure at G 219. -/
theorem bad_0887 : P [282,967,2129,1856,4256,9323,1708] = none := by
  have h0 : G 509 [282,967,2129,1856,4256,9323,1708] = some [395,681,1405,1633,5887,9323,1708] := by simp [G,H]
  have h1 : G 290 [395,681,1405,1633,5887,9323,1708] = some [342,514,1917,1633,5887,9323,1708] := by simp [G,H]
  have hg : G 219 [342,514,1917,1633,5887,9323,1708] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 930, synthetic suffix 5975; failure at G 219. -/
theorem bad_0930 : P [283,906,982,3491,5650,16873,5975] = none := by
  have h0 : G 509 [283,906,982,3491,5650,16873,5975] = some [398,1302,982,3491,5650,16873,5975] := by simp [G,H]
  have h1 : G 290 [398,1302,982,3491,5650,16873,5975] = some [346,1646,982,3491,5650,16873,5975] := by simp [G,H]
  have hg : G 219 [346,1646,982,3491,5650,16873,5975] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨20, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 946, synthetic suffix 1941; failure at G 219. -/
theorem bad_0946 : P [283,906,984,4292,3253,9555,1941] = none := by
  have h0 : G 509 [283,906,984,4292,3253,9555,1941] = some [398,1302,984,4292,3253,9555,1941] := by simp [G,H]
  have h1 : G 290 [398,1302,984,4292,3253,9555,1941] = some [346,1646,984,4292,3253,9555,1941] := by simp [G,H]
  have hg : G 219 [346,1646,984,4292,3253,9555,1941] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 959, synthetic suffix 55; failure at G 509. -/
theorem bad_0959 : P [282,965,1732,7418,3644,12292,55] = none := by
  have hg : G 509 [282,965,1732,7418,3644,12292,55] = none :=
    (G_none_iff_power 509 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,hg]

/-- Phase 979, synthetic suffix 5359; failure at G 290. -/
theorem bad_0979 : P [282,964,974,2637,13534,14349,5359] = none := by
  have h0 : G 509 [282,964,974,2637,13534,14349,5359] = some [395,682,1654,2637,13534,14349,5359] := by simp [G,H]
  have hg : G 290 [395,682,1654,2637,13534,14349,5359] = none :=
    (G_none_iff_power 290 _ (by omega)).mpr ⟨20, by decide⟩
  simp [P,h0,hg]

/-- Phase 996, synthetic suffix 4637; failure at G 219. -/
theorem bad_0996 : P [280,396,743,4056,3944,19648,4637] = none := by
  have h0 : G 509 [280,396,743,4056,3944,19648,4637] = some [394,395,569,2315,6257,19648,4637] := by simp [G,H]
  have h1 : G 290 [394,395,569,2315,6257,19648,4637] = some [344,737,569,2315,6257,19648,4637] := by simp [G,H]
  have hg : G 219 [344,737,569,2315,6257,19648,4637] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨20, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 1006, synthetic suffix 7041; failure at G 219. -/
theorem bad_1006 : P [283,908,2493,4079,5132,14664,7041] = none := by
  have h0 : G 509 [283,908,2493,4079,5132,14664,7041] = some [398,1304,2493,4079,5132,14664,7041] := by simp [G,H]
  have h1 : G 290 [398,1304,2493,4079,5132,14664,7041] = some [346,1648,2493,4079,5132,14664,7041] := by simp [G,H]
  have hg : G 219 [346,1648,2493,4079,5132,14664,7041] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨20, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 1007, synthetic suffix 1894; failure at G 290. -/
theorem bad_1007 : P [282,965,1729,2904,4018,9341,1894] = none := by
  have h0 : G 509 [282,965,1729,2904,4018,9341,1894] = some [395,680,1207,4109,4018,9341,1894] := by simp [G,H]
  have hg : G 290 [395,680,1207,4109,4018,9341,1894] = none :=
    (G_none_iff_power 290 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,h0,hg]

/-- Phase 1010, synthetic suffix 3571; failure at G 219. -/
theorem bad_1010 : P [283,906,984,4292,3251,6296,3571] = none := by
  have h0 : G 509 [283,906,984,4292,3251,6296,3571] = some [398,1302,984,4292,3251,6296,3571] := by simp [G,H]
  have h1 : G 290 [398,1302,984,4292,3251,6296,3571] = some [346,1646,984,4292,3251,6296,3571] := by simp [G,H]
  have hg : G 219 [346,1646,984,4292,3251,6296,3571] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨19, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 1015, synthetic suffix 518; failure at G 219. -/
theorem bad_1015 : P [282,967,2129,1856,4254,3512,518] = none := by
  have h0 : G 509 [282,967,2129,1856,4254,3512,518] = some [395,681,1405,1633,5885,3512,518] := by simp [G,H]
  have h1 : G 290 [395,681,1405,1633,5885,3512,518] = some [342,514,1917,1633,5885,3512,518] := by simp [G,H]
  have hg : G 219 [342,514,1917,1633,5885,3512,518] = none :=
    (G_none_iff_power 219 _ (by omega)).mpr ⟨18, by decide⟩
  simp [P,h0,h1,hg]

/-- Phase 1023, synthetic suffix 318; failure at G 509. -/
theorem bad_1023 : P [282,965,1732,7418,3640,3576,318] = none := by
  have hg : G 509 [282,965,1732,7418,3640,3576,318] = none :=
    (G_none_iff_power 509 _ (by omega)).mpr ⟨18, by decide⟩
  simp [P,hg]

/-! Each case theorem checks a full original S4 three-drain transition by
    unfolding only successful odd-drain branches and using the existing
    universally proved exact binary-power terminal gate. -/
def badWitnesses : List (Nat × Nat) :=
  [(14,2106),(23,6696),(33,2070),(34,3160),(36,3755),(63,2125),(98,1962),(142,5077),(161,15896),(167,7798),(191,54),(193,2255),(211,5360),(215,6328),(242,3569),(270,2105),(279,104),(290,3159),(303,877),(311,40),(343,630),(354,1963),(356,7252),(359,2166),(417,15895),(418,5976),(423,7799),(430,1890),(434,1943),(447,56),(449,2256),(471,6327),(484,4638),(495,1893),(499,583),(511,317),(513,339),(526,2107),(548,3753),(567,39),(575,2126),(599,631),(612,7251),(627,7061),(631,1709),(654,5079),(673,15897),(674,5977),(686,1889),(705,2254),(751,1892),(754,3570),(755,584),(759,519),(801,2069),(855,629),(871,2164),(887,1708),(930,5975),(946,1941),(959,55),(979,5359),(996,4637),(1006,7041),(1007,1894),(1010,3571),(1015,518),(1023,318)]

#print axioms bad_0014
#print axioms bad_0161
#print axioms bad_1023
end S4Sharp6
